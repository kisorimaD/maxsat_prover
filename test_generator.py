"""Integration regressions. Build maxsat_prover with make before running."""
import json
import re
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from stitch_certificate import assemble_certificate
from verifier.check import load_and_check
from verifier.check import Checker, VerificationError
from verifier.arithmetic import vector_weight

ROOT = Path(__file__).resolve().parent


class GeneratorTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.cwd = Path(self.temp.name)
        shutil.copy(ROOT / 'groups3.txt', self.cwd)

    def run_generator(self, command='test', session='', options=()):
        return subprocess.run([str(ROOT / 'maxsat_prover'), *options, command], input=session,
                              text=True, capture_output=True, cwd=self.cwd, timeout=30)

    def test_help_and_tests_preserve_log(self):
        log = self.cwd / 'pre_certificate.jsonl'
        log.write_text('keep this proof\n')
        for command in ('--help', 'unknown-command', 'safety', 'reductions', 'groups3'):
            with self.subTest(command=command):
                result = self.run_generator(command)
                self.assertEqual(result.returncode, int(command == 'unknown-command'), result.stderr)
                self.assertEqual(log.read_text(), 'keep this proof\n')

    def test_eof_and_incomplete_commands(self):
        self.assertEqual(self.run_generator(session='').returncode, 0)
        for session in ('add x', 'set', 'xiao_branch', 'add x 3 2 ANY\naddpos y\n-x\n'):
            with self.subTest(session=session):
                self.assertNotEqual(self.run_generator(session=session).returncode, 0)

    def test_proved_lemma_roundtrip_without_assumptions(self):
        log = self.cwd / 'pre_certificate.jsonl'
        log.write_text('keep this proof\n')
        result = self.run_generator(command='lemmas')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(log.read_text(), 'keep this proof\n')
        leaves = [json.loads(line) for line in result.stdout.splitlines()
                  if line.startswith('{')]
        self.assertEqual(len(leaves), 2)  # both polarities, cached metadata checked in C++
        for index, leaf in enumerate(leaves):
            with self.subTest(index=index):
                self.assertEqual(leaf['kind'], 'lemma')
                record = {'node_id': 1, 'kind': 'strategy',
                          'formula': leaf['formula'], 'proof': leaf}
                source = self.cwd / f'lemma-{index}.jsonl'
                source.write_text(json.dumps(record) + '\n')
                output = self.cwd / f'lemma-{index}.json'
                assemble_certificate(source, output)
                attached = json.loads(output.read_text())['proof']['proof']
                self.assertEqual(attached['kind'], 'local_context')
                self.assertEqual(len(attached['formula']), 7)
                self.assertEqual(len(attached['proof']['formula']), 5)
                self.assertEqual(load_and_check(output).assumptions, [])

    def test_compensated_absorption_roundtrip(self):
        result = self.run_generator(command='absorption')
        self.assertEqual(result.returncode, 0, result.stderr)
        proofs = [json.loads(line) for line in result.stdout.splitlines() if line.startswith('{')]
        self.assertEqual(len(proofs), 4)
        for index, proof in enumerate(proofs):
            with self.subTest(index=index):
                log = self.cwd / f'absorption-{index}.jsonl'
                log.write_text(json.dumps({'node_id': 1, 'kind': 'strategy',
                                          'formula': proof['formula'], 'proof': proof}) + '\n')
                output = self.cwd / f'absorption-{index}.json'
                n, d = (1609, 1250) if index == 3 else (2, 1)
                assemble_certificate(log, output, n, d)
                self.assertEqual(load_and_check(output).assumptions, [])
        vector = Checker(1609, 1250)._strategy(proofs[-1], 'lemma4', 1)
        self.assertLessEqual(vector_weight(vector, 1609, 1250),
                             vector_weight([2, 7], 1609, 1250))

    def test_lemma_export_is_opt_in_and_covers_remaining_formulas(self):
        session = 'assumptions off\nadd x 3 2 ANY\nsimple_branch\nexit\n'
        artifact = self.cwd / 'saved.json'
        ordinary = self.run_generator(session='set 1.2\n' + session)
        self.assertEqual(ordinary.returncode, 0, ordinary.stderr)
        records = [json.loads(line) for line in (self.cwd / 'pre_certificate.jsonl').read_text().splitlines()]
        self.assertNotIn('lemma_export', records[0])
        self.assertFalse(artifact.exists())
        with self.assertRaises(ValueError):
            assemble_certificate(self.cwd / 'pre_certificate.jsonl', self.cwd / 'proof.json')
        enabled = self.run_generator(session=session, options=('--save-lemma', '1.2', str(artifact)))
        self.assertEqual(enabled.returncode, 0, enabled.stderr)
        assemble_certificate(self.cwd / 'pre_certificate.jsonl', self.cwd / 'proof.json')
        definition = json.loads(artifact.read_text())
        self.assertEqual(definition['target'], {'numerator': 6, 'denominator': 5})
        self.assertEqual(sorted(definition['vector']), [2, 3])
        self.assertGreater(vector_weight(definition['vector'], 6, 5), 1)
        self.assertEqual(definition['premises']['imports'], [])
        with self.assertRaises(VerificationError):
            load_and_check(self.cwd / 'proof.json')  # exporting is not a claim that q was beaten
        with self.assertRaisesRegex(ValueError, 'assembly target differs'):
            assemble_certificate(self.cwd / 'pre_certificate.jsonl', self.cwd / 'other.json', 2, 1)

    def test_weight_target_keeps_q_and_retains_stronger_cases_for_export(self):
        artifact = self.cwd / 'weighted.json'
        options = ('--save-lemma', '2', str(artifact))
        for target, closes in (('1', True), ('0.625', True), ('0.6', False)):
            with self.subTest(target=target):
                result = self.run_generator(options=options, session=
                    f'assumptions off\nweight_target {target}\nadd x 3 1 ANY\nsimple_branch\ncache_stats\nexit\n')
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(f'Было отфильтровано [{int(closes)}]', result.stdout)
                assemble_certificate(self.cwd / 'pre_certificate.jsonl', self.cwd / 'proof.json')
                definition = json.loads(artifact.read_text())
                self.assertEqual(definition['target'], {'numerator': 2, 'denominator': 1})
                self.assertEqual(sorted(definition['vector']), [1, 3])
                self.assertEqual(vector_weight(definition['vector'], 2, 1), 0.625)
                self.assertEqual(load_and_check(self.cwd / 'proof.json').assumptions, [])

    def test_weight_target_changes_closing_without_changing_cached_search(self):
        result = self.run_generator(session=
            'assumptions off\nset 2\nweight_target 0.5\nadd x 3 1 ANY\n'
            'xiao_branch 1\ncache_stats\nweight_target 0.55\nxiao_branch 1\ncache_stats\n'
            'weight_target 0.7\nxiao_branch 1\nexit\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('Осталось [1]', result.stdout)
        self.assertIn('Осталось [0]', result.stdout)
        counters = re.findall(r'Strategy cache: hits=(\d+), misses=(\d+)', result.stdout)
        self.assertEqual(len(counters), 2)
        self.assertGreater(int(counters[1][0]), int(counters[0][0]))
        self.assertEqual(counters[1][1], counters[0][1])
        assemble_certificate(self.cwd / 'pre_certificate.jsonl', self.cwd / 'proof.json', 2, 1)
        self.assertEqual(load_and_check(self.cwd / 'proof.json').assumptions, [])

    def test_invalid_weight_targets_are_rejected(self):
        for target in ('0', '-1', 'nan', 'inf', '1e9999', '0x1p0', '0.5bad'):
            with self.subTest(target=target):
                result = self.run_generator(session=f'weight_target {target}\nexit\n')
                self.assertNotEqual(result.returncode, 0)

    def test_assignment_omits_mixed_boundary_clauses_without_extra_decrease(self):
        result = self.run_generator(command='weight')
        self.assertEqual(result.returncode, 0, result.stderr)
        leaves = [json.loads(line) for line in result.stdout.splitlines() if line.startswith('{')]
        self.assertEqual(len(leaves), 1)
        proof = leaves[0]
        self.assertEqual(proof['alternatives'][1]['formula'], [])
        self.assertEqual(proof['alternatives'][1]['decrease'], 1)
        log = self.cwd / 'mixed-tail.jsonl'
        log.write_text(json.dumps({'node_id': 1, 'kind': 'strategy',
                                  'formula': proof['formula'], 'proof': proof}) + '\n')
        assemble_certificate(log, self.cwd / 'proof.json', 2, 1)
        self.assertEqual(load_and_check(self.cwd / 'proof.json').assumptions, [])

    def test_lemma_export_preserves_refinements_and_the_best_found_strategy(self):
        artifact = self.cwd / 'refined.json'
        result = self.run_generator(
            session='assumptions off\nadd x 3 2 ANY\nempty_divide -1\nxiao_branch 1\nexit\n',
            options=('--save-lemma', '1.2', str(artifact)))
        self.assertEqual(result.returncode, 0, result.stderr)
        assemble_certificate(self.cwd / 'pre_certificate.jsonl', self.cwd / 'proof.json')
        definition = json.loads(artifact.read_text())
        self.assertEqual(definition['proof']['kind'], 'refine')
        self.assertEqual(len(definition['proof']['children']), 2)
        checker = Checker(6, 5)
        checked = checker._strategy(definition['proof'], 'lemma.proof', 1)
        self.assertEqual(checked, definition['vector'])
        self.assertEqual(checker.assumptions, [])

    def test_lemma_export_accepts_a_completed_session_and_locks_q(self):
        artifact = self.cwd / 'complete.json'
        options = ('--save-lemma', '2.0', str(artifact))
        result = self.run_generator(session='set 2\nadd x 3 2 ANY\nsimple_branch\nexit\n', options=options)
        self.assertEqual(result.returncode, 0, result.stderr)
        assemble_certificate(self.cwd / 'pre_certificate.jsonl', self.cwd / 'proof.json')
        load_and_check(self.cwd / 'proof.json')
        self.assertEqual(json.loads(artifact.read_text())['target'], {'numerator': 2, 'denominator': 1})
        original = artifact.read_text()
        result = self.run_generator(session='set 1.2\nexit\n', options=options)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('fixed target q', result.stderr)
        self.assertEqual(artifact.read_text(), original)

    def test_lemma_export_rejects_incomplete_coverage_and_preserves_artifact(self):
        artifact = self.cwd / 'incomplete.json'
        artifact.write_text('keep existing lemma')
        result = self.run_generator(
            session='add x 3 2 ANY\nempty_divide -1\ndrop 0\nexit\n',
            options=('--save-lemma', '1.2', str(artifact)))
        self.assertEqual(result.returncode, 0, result.stderr)
        with self.assertRaisesRegex(ValueError, 'missing referenced'):
            assemble_certificate(self.cwd / 'pre_certificate.jsonl', self.cwd / 'proof.json')
        self.assertEqual(artifact.read_text(), 'keep existing lemma')

    def test_invalid_lemma_export_flags_preserve_log(self):
        log = self.cwd / 'pre_certificate.jsonl'
        log.write_text('keep existing log')
        for options in (('--save-lemma',), ('--save-lemma', '1', 'saved.json'),
                        ('--save-lemma', 'nan', 'saved.json'),
                        ('--save-lemma', '1.2x', 'saved.json'),
                        ('--save-lemma', '0x1.8p0', 'saved.json'),
                        ('--save-lemma', '1.2', 'saved.json', '--save-lemma', '1.2', 'other.json')):
            with self.subTest(options=options):
                self.assertNotEqual(self.run_generator(options=options).returncode, 0)
                self.assertEqual(log.read_text(), 'keep existing log')
        self.assertNotEqual(self.run_generator(command='safety',
                            options=('--save-lemma', '1.2', 'saved.json')).returncode, 0)
        self.assertEqual(log.read_text(), 'keep existing log')

    def test_saved_lemma_file_is_loaded_and_spliced_only_at_its_fixed_q(self):
        from test_lemmas import assign_proof
        artifact = self.cwd / 'saved.json'
        result = self.run_generator(session='add x 3 2 ANY\nsimple_branch\nexit\n',
                                    options=('--save-lemma', '1.2', str(artifact)))
        self.assertEqual(result.returncode, 0, result.stderr)
        assemble_certificate(self.cwd / 'pre_certificate.jsonl', self.cwd / 'source-proof.json')
        definition = json.loads(artifact.read_text())
        formula = [[7, {'tail': i, 'kind': 'any'}] for i in range(3)] + [
            [-7, {'tail': i, 'kind': 'any'}] for i in range(3, 5)]
        leaf = {'kind': 'lemma', 'name': definition['id'], 'roles': [7],
                'witness_clauses': [], 'vector': definition['vector'], 'formula': formula}
        parent = assign_proof(formula + [[9]] * 5, 9)
        parent['alternatives'][0]['proof'] = leaf
        log = self.cwd / 'apply.jsonl'
        log.write_text(json.dumps({'node_id': 1, 'kind': 'strategy',
                                  'formula': parent['formula'], 'proof': parent}) + '\n')
        output = self.cwd / 'applied.json'
        command = ['python3', str(ROOT / 'stitch_certificate.py'), str(log), str(output),
                   '--numerator', '6', '--denominator', '5', '--lemma', str(artifact)]
        assembled = subprocess.run(command, cwd=self.cwd, text=True, capture_output=True)
        self.assertEqual(assembled.returncode, 0, assembled.stderr)
        self.assertEqual(load_and_check(output).assumptions, [])
        with self.assertRaisesRegex(ValueError, 'fixed target'):
            assemble_certificate(log, output, 13, 10, lemma_files=[artifact])

    def test_root_any_and_singleton_roundtrip(self):
        for kind in ('ANY', 'SINGLETON'):
            with self.subTest(kind=kind):
                result = self.run_generator(session=f'set 2\nadd x 3 1 {kind}\nsimple_branch\nexit\n')
                self.assertEqual(result.returncode, 0, result.stderr)
                log = self.cwd / 'pre_certificate.jsonl'
                record = json.loads(log.read_text().splitlines()[0])
                self.assertEqual(record['kind'], 'root_family')
                self.assertEqual(record['singleton'], kind == 'SINGLETON')
                output = self.cwd / 'proof.json'
                assemble_certificate(log, output, 2, 1)
                certificate = json.loads(output.read_text())
                self.assertEqual(certificate['format'], 'maxsat-local-proof-v4')
                self.assertEqual(certificate['maximum_clause_size'], -1)
                self.assertEqual(certificate['maximum_variable_occurrences'], -1)
                self.assertEqual(certificate['scope']['kind'],
                                 'local_template_family')
                self.assertNotEqual(certificate['proof']['formula'], [])
                checked = load_and_check(output)
                self.assertEqual(len(checked.assumptions), 0)

    def test_unsupported_additions_rejected(self):
        for session in ('add x 1 3 SINGLETON\n', 'add x 1 4 SINGLETON\n',
                        'add x 3 2 ANY\nadd y 3 2 ANY\n', 'add x 31 2 ANY\n',
                        'addlit 1 3 SINGLETON\n'):
            with self.subTest(session=session):
                self.assertNotEqual(self.run_generator(session=session).returncode, 0)

    def test_addpos_roundtrip(self):
        result = self.run_generator(session='add x 3 2 ANY\naddpos y\n-x\n\nset 2\nsimple_branch\nexit\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        output = self.cwd / 'proof.json'
        assemble_certificate(self.cwd / 'pre_certificate.jsonl', output, 2, 1)
        self.assertGreater(load_and_check(output).strategies, 1)

    def test_addpos_after_tail_split_roundtrip(self):
        result = self.run_generator(session='add x 3 2 ANY\nempty_divide -1\naddpos y\nx\n\nset 2\nsimple_branch\nexit\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        log = self.cwd / 'pre_certificate.jsonl'
        records = [json.loads(line) for line in log.read_text().splitlines()]
        exposures = [node for node in records if node.get('rule') == 'expose_at_clause']
        self.assertTrue(any(any(isinstance(lit, dict) and lit['kind'] == 'nonempty'
                                for lit in node['formula'][node['clause']])
                            for node in exposures))
        output = self.cwd / 'proof.json'
        assemble_certificate(log, output, 2, 1)
        self.assertGreater(load_and_check(output).strategies, 1)

    def test_bounded_root_roundtrip(self):
        for maximum_clause_size in (1, 2, 3):
            with self.subTest(maximum_clause_size=maximum_clause_size):
                result = self.run_generator(
                    session='set 2\nadd x 3 2 ANY\nsimple_branch\nexit\n',
                    options=('--max-clause-size', str(maximum_clause_size)))
                self.assertEqual(result.returncode, 0, result.stderr)
                log = self.cwd / 'pre_certificate.jsonl'
                root_record = json.loads(log.read_text().splitlines()[0])
                self.assertEqual(root_record['maximum_clause_size'],
                                 maximum_clause_size)
                output = self.cwd / f'proof-k{maximum_clause_size}.json'
                assemble_certificate(log, output, 2, 1)
                certificate = json.loads(output.read_text())
                self.assertEqual(certificate['format'], 'maxsat-local-proof-v4')
                self.assertEqual(certificate['maximum_clause_size'],
                                 maximum_clause_size)
                self.assertEqual(certificate['maximum_variable_occurrences'], -1)
                self.assertEqual(certificate['scope']['degree_coverage'],
                                 'certificate_premise')
                self.assertGreater(load_and_check(output).strategies, 0)

    def test_bounded_structural_safety_for_small_k(self):
        for maximum_clause_size in (1, 2, 3):
            with self.subTest(maximum_clause_size=maximum_clause_size):
                result = self.run_generator(
                    command='safety',
                    options=('--max-clause-size', str(maximum_clause_size)))
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_invalid_maximum_clause_size_is_rejected(self):
        for options in (
                ('--max-clause-size', '0'),
                ('--max-clause-size', 'not-an-integer'),
                ('--max-clause-size', str(2 ** 31 - 1)),
                ('--max-clause-size', '3', '--max-clause-size', '3')):
            with self.subTest(options=options):
                result = self.run_generator(command='safety', options=options)
                self.assertNotEqual(result.returncode, 0)

    def test_variable_occurrence_bound_roundtrip(self):
        result = self.run_generator(
            session='set 2\nadd x 2 1 ANY\nsimple_branch\nexit\n',
            options=('--max-variable-occurrences', '3'))
        self.assertEqual(result.returncode, 0, result.stderr)
        log = self.cwd / 'pre_certificate.jsonl'
        root_record = json.loads(log.read_text().splitlines()[0])
        self.assertEqual(root_record['maximum_variable_occurrences'], 3)
        output = self.cwd / 'proof-s3.json'
        assemble_certificate(log, output, 2, 1)
        certificate = json.loads(output.read_text())
        self.assertEqual(certificate['format'], 'maxsat-local-proof-v4')
        self.assertEqual(certificate['maximum_variable_occurrences'], 3)
        self.assertGreater(load_and_check(output).strategies, 0)

    def test_variable_occurrence_bound_rejects_large_degree(self):
        result = self.run_generator(
            session='add x 3 1 ANY\n',
            options=('--max-variable-occurrences', '3'))
        self.assertNotEqual(result.returncode, 0)

    def test_invalid_variable_occurrence_bound_is_rejected(self):
        for options in (
                ('--max-variable-occurrences', '0'),
                ('--max-variable-occurrences', 'not-an-integer'),
                ('--max-variable-occurrences', str(2 ** 31 - 1)),
                ('--max-variable-occurrences', '3',
                 '--max-variable-occurrences', '3')):
            with self.subTest(options=options):
                result = self.run_generator(command='safety', options=options)
                self.assertNotEqual(result.returncode, 0)

    def test_bounded_mode_cannot_enable_assumptions(self):
        result = self.run_generator(
            session='assumptions on\nexit\n',
            options=('--max-clause-size', '3'))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('недоступны', result.stdout)

    def test_old_log_assembles_as_unrestricted_v2(self):
        result = self.run_generator(
            session='set 2\nadd x 3 2 ANY\nsimple_branch\nexit\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        log = self.cwd / 'pre_certificate.jsonl'
        records = [json.loads(line) for line in log.read_text().splitlines()]
        records[0].pop('maximum_clause_size')
        records[0].pop('maximum_variable_occurrences')
        log.write_text(''.join(json.dumps(record) + '\n' for record in records))
        output = self.cwd / 'proof-v2.json'
        assemble_certificate(log, output, 2, 1)
        certificate = json.loads(output.read_text())
        self.assertEqual(certificate['format'], 'maxsat-local-proof-v2')
        self.assertNotIn('maximum_clause_size', certificate)
        self.assertGreater(load_and_check(output).strategies, 0)


if __name__ == '__main__':
    unittest.main()
