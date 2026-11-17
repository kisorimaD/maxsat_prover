from copy import deepcopy
from pathlib import Path
import tempfile
import unittest

from lemma_library import (expand_lemma_applications, save_session_lemma,
                           _proof_variables, _rename_proof)
from test_lemmas import assign_proof, json_formula
from verifier.check import Checker, VerificationError
from verifier.formula import canonical_formula
from verifier.refine import expected_children


SCOPE = [[2,2,False],[3,1,True],[4,1,True]]
TARGET = {'numerator':2,'denominator':1}


def formula(rows):
    return [list(row)+[{'tail':i,'kind':'any'}] for i,row in enumerate(rows)]


class SignedLemmaContextTests(unittest.TestCase):
    def setUp(self):
        root=formula(((2,),(2,),(-2,3),(-2,-3),(3,),(-3,)))
        proof={'kind':'refine','rule':'expose_at_clause','formula':root,
               'variable':4,'clause':0,'degrees':SCOPE}
        children={canonical_formula(f):f for f in expected_children(proof)}
        proof['children']=[{'kind':'strategy','formula':json_formula(f),
                            'proof':assign_proof(json_formula(f),2)} for f in children.values()]
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.definition=save_session_lemma(proof,Path(self.temp.name)/'signed.json',TARGET)
        self.parent=formula(((-4,),(-4,),(-3,),(-3,),(-2,3),(-2,4),(2,3),(2,4)))
        self.application={'kind':'lemma','name':self.definition['id'], 'formula':self.parent,
                          'roles':[-3,2],'witness_clauses':[], 'vector':self.definition['vector'],
                          'degree_scope':SCOPE}

    def attached(self):
        return expand_lemma_applications(self.application,{self.definition['id']:self.definition},target=TARGET)

    def check(self,proof):
        Checker(**TARGET).check({'kind':'strategy','formula':proof['formula'],'proof':proof})

    def test_negative_instantiation_preserves_the_structural_case_tree(self):
        p=self.attached();self.check(p)
        self.assertEqual({r['literal'] for r in p['role_bindings']},{-3,2})
        self.assertTrue(all(r['variable']>4 for r in p['role_bindings']))
        self.assertEqual(len(p['proof']['children']),len(self.definition['proof']['children']))
        self.assertEqual(Checker(**TARGET)._strategy(p,'signed',1),[2,2])
        # Renaming the outer variables updates the bindings, without changing
        # the formal parameters' polarity inside the structural proof.
        mapping={v:v+100 for v in _proof_variables(p)};mapping[3]=-103
        self.check(_rename_proof(p,mapping,100))

    def test_forged_binding_capture_and_missing_binding_are_rejected(self):
        for edit in ('sign','duplicate','not_fresh','missing','capture'):
            p=deepcopy(self.attached())
            if edit=='sign':p['role_bindings'][0]['literal']*=-1
            elif edit=='duplicate':p['role_bindings'][1]['literal']=p['role_bindings'][0]['literal']
            elif edit=='not_fresh':p['role_bindings'][0]['variable']=2
            elif edit=='missing':p.pop('role_bindings')
            else:p['proof']['children'][0]['proof']['variable']=4
            with self.subTest(edit=edit),self.assertRaises(VerificationError):self.check(p)

    def test_bound_proof_can_be_saved_and_used_as_the_next_lemma(self):
        saved=save_session_lemma(self.attached(),Path(self.temp.name)/'next.json',TARGET)
        target=_rename_proof({'kind':'call','formula':self.parent},{2:-12,3:13,4:14},100)['formula']
        application={'kind':'lemma','name':saved['id'],'roles':[-12,13,14],
                     'formula':target,'witness_clauses':[],'vector':saved['vector'],'degree_scope':SCOPE}
        self.check(expand_lemma_applications(application,{saved['id']:saved},target=TARGET))


if __name__=='__main__':unittest.main()
