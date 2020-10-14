from collections import OrderedDict
from unittest import TestCase

from parsimonious import VisitationError

from latex_to_smt import LatexVisitor, clean
from inferred_types import *

class TestLatexVisitor(TestCase):
    def setUp(self):
        self.lv = LatexVisitor({})

    def test_get_definitions(self):
        output = self.lv.parse("(x\\landy)")
        output = self.lv.get_definitions() + output
        success = "(declare-const x Bool)\n(declare-const y Bool)\n(and x y)" == output \
                  or "(declare-const y Bool)\n(declare-const x Bool)\n(and x y)" == output
        self.assertEqual(True, success)

    def test_visit_varint(self):
        output = self.lv.parse("x")
        self.assertEqual("x", output)

        output = self.lv.parse("3")
        self.assertEqual("3", output)

    def test_visit_var(self):
        output = self.lv.parse("x", hide_type=False)
        self.assertEqual(("x", unknown), output)

        # With _
        self.setUp()
        output = self.lv.parse("x_i", hide_type=False)
        self.assertEqual(("x_i", unknown), output)

        # With _{x}
        self.setUp()
        output = self.lv.parse("x_{i}", hide_type=False)
        self.assertEqual(("x_i", unknown), output)

        # With _{x,y}
        self.setUp()
        output = self.lv.parse("x_{y,z}", hide_type=False)
        self.assertEqual(("x_y_z", unknown), output)

        # With _0
        self.setUp()
        output = self.lv.parse("x_0", hide_type=False)
        self.assertEqual(("x_0", unknown), output)

        # With _{y,0,86,z}
        self.setUp()
        output = self.lv.parse("x_{y,0,86,z}", hide_type=False)
        self.assertEqual(("x_y_0_86_z", unknown), output)

    def test_visit_int(self):
        output = self.lv.parse("10", hide_type=False)
        self.assertEqual(("10", num), output)

        output = self.lv.parse(".5542", hide_type=False)
        self.assertEqual(("0.5542", real), output)

    # TODO: implement reals
    # def test_visit_int_realint(self):
    #     output = self.lv.parse("0.1")
    #     self.assertEqual("0.1", output)
    #
    #     output = self.lv.parse("30.7531")
    #     self.assertEqual("30.7531", output)
    #
    #     output = self.lv.parse(".1")
    #     self.assertEqual(".1", output)

    def test_visit_ite(self):
        output = self.lv.parse("\\T{if}x\\T{then}(y\\landz)\\T{else}z")
        self.assertEqual("(ite x (and y z) z)", output)

    def test_visit_complex_ite(self):
        self.lv.global_vars = {"R": 5}
        output = self.lv.parse("(2=\\T{if}(2=x)\\T{then}1\\T{else}0)")
        self.assertEqual("(= 2 (ite (= 2 x) 1 0))", output)

    def test_visit_wedge_int_bounds(self):
        # # Low variant
        # output = self.iv.parse("\\bigwedge_{i:1<i<2}i")
        # output = output.replace("\n", "").replace("\r\n", "")
        # self.assertEqual("(and(and x_1 y_1 (= x z_1))(and x_2 y_2 (= x z_2)))", output)
        # self.fail()

        # Lower and upper variant
        output = self.lv.parse("\\bigwedge_{i=1}^{3}(x_i\\landy_i\\land(x=z_i))")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(and(and x_1 y_1 (= x z_1))(and x_2 y_2 (= x z_2)))", output)

    def test_visit_wedge_global_var_bounds(self):
        self.setUp()
        self.lv.global_vars = {"x": 1, "y": 3}
        output = self.lv.parse("\\bigwedge_{i=x}^{y}(x_i\\landy_i\\land(x=z_i))")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(and(and x_1 y_1 (= x z_1))(and x_2 y_2 (= x z_2)))", output)

    def test_visit_wedge_varint_bounds(self):
        # Using simple global arithmetic
        self.lv.global_vars = {"x": 1, "y": 3}
        output = self.lv.parse("\\bigwedge_{i=y-2}^{x+2}(x_i\\landy_i\\land(x=z_i))")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(and(and x_1 y_1 (= x z_1))(and x_2 y_2 (= x z_2)))", output)

    def test_visit_wedge_complex_var(self):
        self.lv.global_vars = {"x": 1, "y": 3}
        output = self.lv.parse("\\bigwedge_{i=0}^{2}\\bigwedge_{j=0}^{2}(x_{i,j}\\landy_i\\land(x=z_i))")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual(
            "(and(and(and x_0_0 y_0 (= x z_0))(and x_0_1 y_0 (= x z_0)))(and(and x_1_0 y_1 (= x z_1))(and x_1_1 y_1 (= x z_1))))",
            output)

    def test_visit_wedge_subset_var(self):
        output = self.lv.parse("\\bigwedge_{xi=0}^{2}\\bigwedge_{x=0}^{2}\\bigwedge_{i=0}^{2}x_{xi,i,x}")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual(
            "(and(and(andx_0_0_0x_0_1_0)(andx_0_0_1x_0_1_1))(and(andx_1_0_0x_1_1_0)(andx_1_0_1x_1_1_1)))",
            output)

    def test_visit_wedge_subset_neighbour(self):
        output = self.lv.parse("\\bigwedge_{xi=0}^{2}x_{xi,xi}")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(andx_0_0x_1_1)", output)

    def test_visit_vee(self):
        # Lower and upper variant
        output = self.lv.parse("\\bigvee_{i=1}^{3}(x_i\\landy_i\\land(x=z_i))")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(or(and x_1 y_1 (= x z_1))(and x_2 y_2 (= x z_2)))", output)

    def test_visit_vee_replace_explicit(self):
        # Without marking i for replacement, i is not replaced.
        output = self.lv.parse("\\bigvee_{i=0}^{3}i")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(oriii)", output)

        self.setUp()
        # When marking i for replacement, i is replaced and not added to variables.
        output = self.lv.parse("\\bigvee_{i=0}^{3}\\markreplaceable{i}")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(or012)", output)
        self.assertNotIn("i", self.lv.variables)

    def test_visit_sum(self):
        output = self.lv.parse("\\sum_{i=1}^{3}(x_i-3)")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(+(- x_1 3)(- x_2 3))", output)

    def test_visit_rwedge(self):
        # Lowup variant is equivalent to the lower and upper variant
        output_normal_wedge = self.lv.parse("\\bigwedge_{i=0}^{3}x_i")
        output = self.lv.parse("\\bigwedge_{i:0\\leqi<3}x_i")
        output_normal_wedge = output_normal_wedge.replace("\n", "").replace("\r\n", "")
        output = output.replace("\n", "").replace("\r\n", "")
        print("HENK")
        # Lowup variant with 2 variables
        self.setUp()
        output = self.lv.parse("\\bigwedge_{i,j:0\\leqi<j<3}(x_i\\landx_j)")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(and(=> (distinct 0 1) (and x_0 x_1))(=> (distinct 1 1) (and x_1 x_1))(=> (distinct 0 2) ("
                         "and x_0 x_2))(=> (distinct 1 2) (and x_1 x_2)))", output)
        print("ARNOLD")
        # Lowup variant with 3 variables
        self.setUp()
        output = self.lv.parse("\\bigwedge_{i,j,k:0\\leqi<j<k<4}x_{i,j,k}")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(and(=> (distinct 0 1 2) x_0_1_2)(=> (distinct 1 1 2) x_1_1_2)(=> (distinct 0 2 2) "
                         "x_0_2_2)(=> (distinct 1 2 2) x_1_2_2)(=> (distinct 0 1 3) x_0_1_3)(=> (distinct 1 1 3) "
                         "x_1_1_3)(=> (distinct 0 2 3) x_0_2_3)(=> (distinct 1 2 3) x_1_2_3))",
                         output)

    def test_visit_indirect_type_inference(self):
        # Num
        output = self.lv.parse("(a=1)")
        self.assertEqual("Num", self.lv.variables.get("a"))

        self.setUp()
        # Real
        output = self.lv.parse("(a=1.1)")
        self.assertEqual("Real", self.lv.variables.get("a"))

        self.setUp()
        # Complex
        output = self.lv.parse("(b=(c\\landd))")
        self.assertEqual(OrderedDict([('b', 'Bool'), ('c', 'Bool'), ('d', 'Bool')]), self.lv.variables)

    def test_visit_rvee(self):
        output = self.lv.parse("\\bigvee_{i,j,k:0\\leqi<j<k<4}x_{i,j,k}")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(or(=> (distinct 0 1 2) x_0_1_2)(=> (distinct 1 1 2) x_1_1_2)(=> (distinct 0 2 2) x_0_2_2)("
                         "=> (distinct 1 2 2) x_1_2_2)(=> (distinct 0 1 3) x_0_1_3)(=> (distinct 1 1 3) x_1_1_3)(=> ("
                         "distinct 0 2 3) x_0_2_3)(=> (distinct 1 2 3) x_1_2_3))",
                         output)

    def test_visit_rvee_wrong_inequalities(self):
        self.assertRaisesRegex(VisitationError, ".*ValueError.*", self.lv.parse,
                               "\\bigvee_{i,ii:0\\leqi<ii<k<4}x_{i,ii}")

    def test_visit_rvee_wrong_localvars(self):
        self.assertRaisesRegex(VisitationError, ".*ValueError.*", self.lv.parse,
                               "\\bigvee_{i,ii,k,h:0\\leqi<ii<k<4}x_{i,ii}")

    def test_visit_subset_vars(self):
        self.lv.parse("\\bigvee_{i,iii,ii:0\\leqiii<ii<i<4}x_{i,ii}")
        self.assertGreater(len(self.lv.variables), 0)
        for i in self.lv.variables:
            for j in ["i", "ii", "iii"]:
                self.assertNotIn(j, i)

        self.lv.parse("\\bigwedge_{hi=0}^{1}\\bigwedge_{h=0}^{1}p_{hi,h}")
        for i in self.lv.variables:
            for j in ["hi", "i"]:
                self.assertNotIn(j, i)

    def test_visit_substring_vars(self):
        output = self.lv.parse("\\bigwedge_{i=0}^{2}a_{i+1+1}")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(anda_2a_3)", output)

    def test_visit_rsum(self):
        output = self.lv.parse("\\sum_{i,j,k:0\\leqi<j<k<4}x_{i,j,k}")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(+(=> (distinct 0 1 2) x_0_1_2)(=> (distinct 1 1 2) x_1_1_2)(=> (distinct 0 2 2) x_0_2_2)("
                         "=> (distinct 1 2 2) x_1_2_2)(=> (distinct 0 1 3) x_0_1_3)(=> (distinct 1 1 3) x_1_1_3)(=> ("
                         "distinct 0 2 3) x_0_2_3)(=> (distinct 1 2 3) x_1_2_3))",
                         output)

    def test_visit_and(self):
        output = self.lv.parse("(x\\landy)", hide_type=False)
        self.assertEqual(("(and x y)", boolean), output)

        output = self.lv.parse("(x\\landy\\landz)", hide_type=False)
        self.assertEqual(("(and x y z)", boolean), output)

        output = self.lv.parse("(x\\land(y\\landz))")
        self.assertEqual("(and x (and y z))", output)

    def test_visit_or(self):
        output = self.lv.parse("(x\\lory)")
        self.assertEqual("(or x y)", output)

        output = self.lv.parse("(x\\lory\\lorz)")
        self.assertEqual("(or x y z)", output)

    def test_visit_equals(self):
        output = self.lv.parse("(x=y)")
        self.assertEqual("(= x y)", output)

        output = self.lv.parse("(x=y=z)")
        self.assertEqual("(= x y z)", output)

    def test_visit_geq(self):
        List = range(10)
        output = self.lv.parse("(4\\geqy)")
        self.assertEqual("(>= 4 y)", output)

    def test_visit_rexpr(self):
        output = self.lv.parse("(x=y)")
        self.assertEqual("(= x y)", output)

    def test_visit_not(self):
        output = self.lv.parse("\\lnotx")
        self.assertEqual("(not x)", output)
        self.assertEqual({"x": "Bool"}, self.lv.variables)

        self.setUp()
        output = self.lv.parse("\\lnot(x\\landy)")
        self.assertEqual("(not (and x y))", output)

    def test_visit_neq(self):
        output = self.lv.parse("(x\\neqy)")
        self.assertEqual("(distinct x y)", output)

        output = self.lv.parse("(x\\neq(y\\landz))")
        self.assertEqual("(distinct x (and y z))", output)

        output = self.lv.parse("(x\\neq(y\\neqz))")
        self.assertEqual("(distinct x (distinct y z))", output)

        output = self.lv.parse("(w\\neqx\\neqy\\neqz)")
        self.assertEqual("(distinct w x y z)", output)

    def test_visit_equals_and_and(self):
        output = self.lv.parse("((x=y)\\landx\\land(y=z))")
        self.assertEqual("(and (= x y) x (= y z))", output)

    def test_visit_vee_and_wedge(self):
        output = self.lv.parse("\\bigwedge_{i=1}^{3}\\bigvee_{j=0}^{2}(x_i\\landy_i\\landj\\land(x=z_i=j_j=g_j))")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual(
            "(and(or(and x_1 y_1 j (= x z_1 j_0 g_0))(and x_1 y_1 j (= x z_1 j_1 g_1)))(or(and x_2 y_2 j (= x z_2 j_0 g_0))(and x_2 y_2 j (= x z_2 j_1 g_1))))",
            output)

    def test_globals_dont_inherently_stay_as_definitions(self):
        self.lv.global_vars = {"R": 3}
        self.lv.parse("x")
        self.assertIn("x", self.lv.variables)
        self.assertEqual(None, self.lv.variables.get("x"))
        self.assertNotIn("R", self.lv.variables)

        # If the global is explicitly used then it should be defined.
        self.setUp()
        self.lv.global_vars = {"R": 3}
        self.lv.parse("R")
        self.assertIn("R", self.lv.variables)
        self.assertEqual(None, self.lv.variables.get("R"))

        # If the global is present in a reduciblevarint it should be defined.
        self.setUp()
        self.lv.global_vars = {"R": 3}
        self.lv.parse("\\bigvee_{i=0}^{R}x")
        self.assertIn("x", self.lv.variables)
        self.assertEqual(None, self.lv.variables.get("x"))
        self.assertIn("R", self.lv.variables)
        self.assertEqual(None, self.lv.variables.get("R"))

    def test_variable_type_inference_lexpr(self):
        # Test whether the left expression is properly assigned.
        self.lv.parse("(x\\landy)")
        self.assertIn("x", self.lv.variables)
        self.assertEqual("Bool", self.lv.variables.get("x"))

        self.setUp()
        self.lv.parse("((x\\lorz)=(y\\lorz))")
        self.assertIn("x", self.lv.variables)
        self.assertEqual("Bool", self.lv.variables.get("x"))
        self.assertIn("y", self.lv.variables)
        self.assertEqual("Bool", self.lv.variables.get("y"))

    def test_variable_type_inference_rexpr(self):
        self.lv.parse("(x\\landy)")
        self.assertIn("y", self.lv.variables)
        self.assertEqual("Bool", self.lv.variables.get("y"))

        self.setUp()
        self.lv.parse("((z\\lorx)=(z=y))")

        self.assertIn("x", self.lv.variables)
        self.assertEqual("Bool", self.lv.variables.get("x"))
        self.assertIn("y", self.lv.variables)
        self.assertEqual(None, self.lv.variables.get("y"))
        self.assertIn("z", self.lv.variables)
        self.assertEqual("Bool", self.lv.variables.get("z"))

    def test_variable_type_inference_ambiguous(self):
        self.lv.parse("(x=y)")
        self.assertIn("x", self.lv.variables)
        self.assertEqual(None, self.lv.variables.get("x"))
        self.assertIn("y", self.lv.variables)
        self.assertEqual(None, self.lv.variables.get("x"))
