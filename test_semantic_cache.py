from itertools import product
import unittest
import numpy as np

from verifier.formula import normalize_formula,satisfied_clauses,variables
from verifier.semantic import optimum_vector,_cached_optimum_vector


class SemanticCacheTests(unittest.TestCase):
    def test_boundary_bit_order_alpha_renaming_and_mutable_results(self):
        a=normalize_formula([[2,('tail',7,'any')],[-2,('tail',3,'any')],[3]])
        _cached_optimum_vector.cache_clear()
        original=optimum_vector(a,[7,3,99])
        renamed=normalize_formula([[12,('tail',41,'any')],[-12,('tail',19,'any')],[14]])
        self.assertTrue(np.array_equal(original,optimum_vector(renamed,[41,19,87])))
        self.assertGreater(_cached_optimum_vector.cache_info().hits,0)
        original[0]=-100
        self.assertNotEqual(optimum_vector(a,[7,3,99])[0],-100)
        for order in ([7,3,99],[3,99,7]):
            actual=optimum_vector(a,order)
            for mask in range(8):
                boundary={v:bool(mask&(1<<i)) for i,v in enumerate(order)}
                expected=max(satisfied_clauses(a,dict(zip(variables(a),vals)),boundary)
                             for vals in product((False,True),repeat=2))
                self.assertEqual(actual[mask],expected)


if __name__=='__main__':unittest.main()
