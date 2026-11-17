"""Native saved-lemma loading, matching, policy and proof round trips."""
from copy import deepcopy
import json
import unittest

from lemma_library import save_session_lemma, expand_lemma_applications, definition_digest
from stitch_certificate import assemble_certificate
import test_generator as generator_tests
from test_lemmas import assign_proof, json_formula
from verifier.check import Checker, VerificationError, load_and_check
from verifier.formula import canonical_formula
from verifier.refine import expected_children, POSSIBLE_DEGREES


TARGET = {'numerator': 12873, 'denominator': 10000}


class SavedLemmaGeneratorTests(unittest.TestCase):
    setUp = generator_tests.GeneratorTests.setUp
    run_generator = generator_tests.GeneratorTests.run_generator

    def save(self, name, proof, target=TARGET):
        path = self.cwd / name
        save_session_lemma(proof, path, target)
        return path

    def imported_source(self):
        path = self.cwd / 'source.json'
        result = self.run_generator(session='add x 2 1 SINGLETON\nxiao_branch 0\nexit\n',
                                    options=('--save-lemma', '1.2872', str(path)))
        self.assertEqual(result.returncode, 0, result.stderr)
        assemble_certificate(self.cwd / 'pre_certificate.jsonl', self.cwd / 'source-proof.json')
        return path

    def leaves(self, proof):
        yield proof
        if 'proof' in proof:
            yield from self.leaves(proof['proof'])
        for child in proof.get('children', []):
            yield from self.leaves(child)
        for alternative in proof.get('alternatives', []):
            yield from self.leaves(alternative['proof'])

    def test_generator_reuses_saved_imported_lemma_and_assembly_finds_its_file(self):
        source = self.imported_source()
        definition = json.loads(source.read_text())
        self.assertEqual(definition['vector'], [1, 8])
        result = self.run_generator(options=('--lemma', str(source)), session=
                                    'set 1.2872\nadd x 2 1 SINGLETON\nxiao_branch 0\nlemma_stats\nexit\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('loaded=1, attempts=1, matches=1', result.stdout)
        records = [json.loads(line) for line in (self.cwd / 'pre_certificate.jsonl').read_text().splitlines()]
        self.assertEqual(records[0]['lemma_sources'][0]['path'], str(source))
        leaf = records[1]['proof']
        self.assertEqual(leaf['kind'], 'lemma')
        self.assertEqual(leaf['name'], definition['id'])
        self.assertEqual(leaf['definition_digest'], definition_digest(definition))
        output = self.cwd / 'proof.json'
        assemble_certificate(self.cwd / 'pre_certificate.jsonl', output)
        checked = load_and_check(output)
        self.assertEqual([assumption['name'] for assumption in checked.assumptions], ['lemma3'])

    def test_imported_lemma_is_disabled_by_assumptions_off_and_at_other_q(self):
        source = self.imported_source()
        for strict, q in ((True, '1.2872'), (False, '1.3'),
                          (False, '1.287200000000000000000001')):
            with self.subTest(strict=strict, q=q):
                session = ('assumptions off\n' if strict else '') + \
                          f'set {q}\nadd x 2 1 SINGLETON\nxiao_branch 0\nlemma_stats\nset 2\nsimple_branch\nexit\n'
                result = self.run_generator(options=('--lemma', str(source)), session=session)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('loaded=1, attempts=0, matches=0', result.stdout)
                records = [json.loads(line) for line in (self.cwd / 'pre_certificate.jsonl').read_text().splitlines()]
                self.assertFalse(any(node['kind'] == 'lemma' for record in records[1:] for node in self.leaves(record)))
                output = self.cwd / 'proof.json'
                assemble_certificate(self.cwd / 'pre_certificate.jsonl', output, 2, 1)
                checked = load_and_check(output)
                if strict:
                    self.assertEqual(checked.assumptions, [])

    def test_multi_role_signed_matching_and_cached_tail_renaming(self):
        tail = lambda i, kind='any': {'tail': i, 'kind': kind}
        formula = [[2, 5, tail(0, 'nonempty')], [-2, 5, tail(1)], [5, tail(2)],
                   [-5], [-5, tail(3)], [2, tail(4)], [-2, tail(5)]]
        source = self.save("two ' roles.json", {'kind': 'call', 'formula': formula})
        result = self.run_generator(command='saved_lemmas', options=('--lemma', str(source)))
        self.assertEqual(result.returncode, 0, result.stderr)
        leaves = [json.loads(line) for line in result.stdout.splitlines() if line.startswith('{')]
        self.assertEqual([leaf['roles'] for leaf in leaves], [[3, 7], [3, -7]])
        for index, leaf in enumerate(leaves):
            self.assertEqual(leaf['witness_clauses'], [3])
            parent = assign_proof(leaf['formula'] + [[99]] * 5, 99)
            parent['alternatives'][0]['proof'] = leaf
            log = self.cwd / f'fixture-{index}.jsonl'
            log.write_text(json.dumps({'node_id': 1, 'kind': 'strategy',
                                       'formula': parent['formula'], 'proof': parent}) + '\n')
            output = self.cwd / f'fixture-{index}.json'
            assemble_certificate(log, output, **TARGET, lemma_files=[source])
            self.assertEqual(load_and_check(output).assumptions, [])

    def exposure_source(self, name, degrees):
        formula = [[2, {'tail': i, 'kind': 'any'}] for i in range(3)] + [
            [-2, {'tail': i, 'kind': 'any'}] for i in range(3, 5)]
        proof = {'kind': 'refine', 'rule': 'expose_at_clause', 'variable': 3,
                 'formula': formula, 'clause': 0, 'degrees': degrees}
        unique = {canonical_formula(child): child for child in expected_children(proof)}
        proof['children'] = [{'kind': 'call', 'formula': json_formula(child)} for child in unique.values()]
        return self.save(name, proof)

    def test_degree_scope_filters_native_matches_and_survives_resaving(self):
        source = self.exposure_source('narrow proof.json', [[2, 2, False]])
        broad = self.run_generator(command='saved_lemmas', options=('--lemma', str(source)))
        self.assertEqual(broad.returncode, 0, broad.stderr)
        self.assertFalse(any(line.startswith('{') for line in broad.stdout.splitlines()))
        output = self.cwd / 'resaved.json'
        result = self.run_generator(options=('--lemma', str(source), '--save-lemma', '1.2873', str(output)),
                                    session='sv 0100000\nadd x 3 2 ANY\nxiao_branch 0\nlemma_stats\nexit\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('matches=1', result.stdout)
        assemble_certificate(self.cwd / 'pre_certificate.jsonl', self.cwd / 'proof.json')
        resaved = json.loads(output.read_text())
        self.assertEqual(resaved['proof']['proof']['degree_scope'], [[2, 2, False]])
        self.assertTrue(resaved['premises']['degrees'])
        # A forged broader application is rejected independently of matching.
        bad = deepcopy(resaved['proof']['proof'])
        bad['degree_scope'].append([3, 2, False])
        with self.assertRaisesRegex(VerificationError, 'does not cover'):
            Checker(**TARGET)._strategy(bad, 'proof', 1)

    def test_forgotten_literal_degrees_are_checked_by_the_verifier(self):
        source = self.exposure_source('wide.json', [list(degree) for degree in POSSIBLE_DEGREES])
        definition = json.loads(source.read_text())
        result = self.run_generator(command='saved_lemmas', options=('--lemma', str(source)))
        self.assertEqual(result.returncode, 0, result.stderr)
        leaves = [json.loads(line) for line in result.stdout.splitlines() if line.startswith('{')]
        self.assertEqual(len(leaves), 2)
        attached = expand_lemma_applications(leaves[0], {definition['id']: definition}, target=TARGET)
        self.assertEqual(Checker(**TARGET)._strategy(attached, 'proof', 1), [0])
        bad = deepcopy(attached)
        bad['degree_scope'] = [[3, 2, False], [2, 3, False]]
        with self.assertRaisesRegex(VerificationError, 'forgotten literal'):
            Checker(**TARGET)._strategy(bad, 'proof', 1)

    def test_failed_loading_preserves_log_and_duplicate_ids_are_rejected(self):
        source = self.save('valid.json', {'kind': 'call', 'formula': [[2], [-2]]})
        definition = json.loads(source.read_text())
        log = self.cwd / 'pre_certificate.jsonl'
        log.write_text('keep original log')
        bad = self.cwd / 'bad.json'
        for mutation in (lambda d: d.__setitem__('vector', [9]),
                         lambda d: d.__setitem__('premises', {}),
                         lambda d: d.__setitem__('id', 'step5.1')):
            malformed = deepcopy(definition)
            mutation(malformed)
            bad.write_text(json.dumps(malformed))
            result = self.run_generator(options=('--lemma', str(bad)), session='exit\n')
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('lemma loading failed', result.stderr)
            self.assertEqual(log.read_text(), 'keep original log')
        bad.write_text(source.read_text())
        result = self.run_generator(options=('--lemma', str(source), '--lemma', str(bad)), session='exit\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('duplicate saved lemma identifiers', result.stderr)
        self.assertEqual(log.read_text(), 'keep original log')
        result = self.run_generator(options=('--lemma', str(self.cwd / 'missing.json')), session='exit\n')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(log.read_text(), 'keep original log')

    def test_changed_artifact_is_rejected_but_an_explicit_frozen_copy_can_be_used(self):
        source = self.imported_source()
        frozen = self.cwd / 'frozen.json'
        frozen.write_text(source.read_text())
        result = self.run_generator(options=('--lemma', str(source)), session=
                                    'set 1.2872\nadd x 2 1 SINGLETON\nxiao_branch 0\nexit\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        changed = json.loads(source.read_text())
        changed['id'] = 'session:changed'
        source.write_text(json.dumps(changed))
        log = self.cwd / 'pre_certificate.jsonl'
        output = self.cwd / 'proof.json'
        with self.assertRaisesRegex(ValueError, 'changed since generation'):
            assemble_certificate(log, output)
        assemble_certificate(log, output, lemma_files=[frozen])
        self.assertEqual(len(load_and_check(output).assumptions), 1)


if __name__ == '__main__':
    unittest.main()
