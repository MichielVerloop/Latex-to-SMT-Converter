from unittest import TestCase
from latex_to_smt import LatexVisitor


class TestLatexVisitor(TestCase):
    def setUp(self):
        self.lv = LatexVisitor({})

    def test_get_definitions(self):
        output = self.lv.parse("(x\\landy)")
        output = self.lv.get_definitions() + output
        success = "(declare-const x Int)\n(declare-const y Int)\n(and x y)" == output or "(declare-const y Int)\n(declare-const x Int)\n(and x y)" == output
        self.assertEqual(True, success)

    def test_visit_varint(self):
        output = self.lv.parse("x")
        self.assertEqual("x", output)

        output = self.lv.parse("3")
        self.assertEqual("3", output)

    def test_visit_var(self):
        output = self.lv.parse("x")
        self.assertEqual("x", output)

        # With _
        self.setUp()
        output = self.lv.parse("x_i")
        self.assertEqual("x_i", output)

        # With _{x}
        self.setUp()
        output = self.lv.parse("x_{i}")
        self.assertEqual("x_i", output)

        # With _{x,y}
        self.setUp()
        output = self.lv.parse("x_{y,z}")
        self.assertEqual("x_y_z", output)

        # With _0
        self.setUp()
        output = self.lv.parse("x_0")
        self.assertEqual("x_0", output)

        # With _{y,0,86,z}
        self.setUp()
        output = self.lv.parse("x_{y,0,86,z}")
        self.assertEqual("x_y_0_86_z", output)

    def test_visit_int(self):
        output = self.lv.parse("0")
        self.assertEqual("0", output)

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
        print(output)
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual(
            "(and(and(andx_0_0_0x_0_1_0)(andx_0_0_1x_0_1_1))(and(andx_1_0_0x_1_1_0)(andx_1_0_1x_1_1_1)))",
            output)

    def test_visit_wedge_subset_neighbour(self):
        output = self.lv.parse("\\bigwedge_{xi=0}^{2}x_{xi,xi}")
        print(output)
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(andx_0_0x_1_1)", output)

    def test_visit_vee(self):
        # Lower and upper variant
        output = self.lv.parse("\\bigvee_{i=1}^{3}(x_i\\landy_i\\land(x=z_i))")
        print(output)
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(or(and x_1 y_1 (= x z_1))(and x_2 y_2 (= x z_2)))", output)

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
        self.assertEqual(output_normal_wedge, output)

        # Lowup variant with 2 variables
        self.setUp()
        output = self.lv.parse("\\bigwedge_{i,j:0\\leqi<j<3}(x_i\\landx_j)")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(and(and x_0 x_1)(and x_0 x_2)(and x_1 x_1)(and x_1 x_2))", output)

        # Lowup variant with 3 variables
        self.setUp()
        output = self.lv.parse("\\bigwedge_{i,j,k:0\\leqi<j<k<4}x_{i,j,k}")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(andx_0_1_2x_0_1_3x_0_2_2x_0_2_3x_1_1_2x_1_1_3x_1_2_2x_1_2_3)", output)

    def test_visit_rvee(self):
        output = self.lv.parse("\\bigvee_{i,j,k:0\\leqi<j<k<4}x_{i,j,k}")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(orx_0_1_2x_0_1_3x_0_2_2x_0_2_3x_1_1_2x_1_1_3x_1_2_2x_1_2_3)", output)

    def test_visit_rsum(self):
        output = self.lv.parse("\\sum_{i,j,k:0\\leqi<j<k<4}x_{i,j,k}")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(+x_0_1_2x_0_1_3x_0_2_2x_0_2_3x_1_1_2x_1_1_3x_1_2_2x_1_2_3)", output)

    def test_visit_and(self):
        output = self.lv.parse("(x\\landy\\landz)")
        self.assertEqual("(and x y z)", output)

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
        output = self.lv.parse("(4\\geqy)")
        self.assertEqual("(>= 4 y)", output)

    def test_visit_rexpr(self):
        output = self.lv.parse("(x=y)")
        self.assertEqual("(= x y)", output)

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
        self.assertNotIn("R", self.lv.variables)

        # If the global is explicitly used then it should be defined.
        self.setUp()
        self.lv.global_vars = {"R": 3}
        self.lv.parse("R")
        self.assertIn("R", self.lv.variables)

        # If the global is present in a reduciblevarint it should be defined.
        self.setUp()
        self.lv.global_vars = {"R": 3}
        self.lv.parse("\\bigvee_{i=0}^{R}x")
        self.assertIn("R", self.lv.variables)
        self.assertIn("x", self.lv.variables)
