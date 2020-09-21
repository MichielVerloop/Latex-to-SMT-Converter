from unittest import TestCase
from latex_to_smt import LatexVisitor


class TestLatexVisitor(TestCase):
    def setUp(self):
        self.lv = LatexVisitor({})

    def test_get_definitions(self):
        output = self.lv.parse("(x\landy)")
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

    def test_visit_int(self):
        output = self.lv.parse("0")
        self.assertEqual("0", output)

    #TODO: implement reals
    # def test_visit_int_realint(self):
    #     output = self.lv.parse("0.1")
    #     self.assertEqual("0.1", output)
    #
    #     output = self.lv.parse("30.7531")
    #     self.assertEqual("30.7531", output)
    #
    #     output = self.lv.parse(".1")
    #     self.assertEqual(".1", output)



    def test_visit_wedge_int_bounds(self):
        # # Low variant
        # output = self.iv.parse("\\bigwedge_{i:1<i<2}i")
        # output = output.replace("\n", "").replace("\r\n", "")
        # self.assertEqual("(and(and x_1 y_1 (= x z_1))(and x_2 y_2 (= x z_2)))", output)
        # self.fail()

        # Lower and upper variant
        output = self.lv.parse("\\bigwedge_{i=1}^{3}(x_i\landy_i\land(x=z_i))")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(and(and x_1 y_1 (= x z_1))(and x_2 y_2 (= x z_2)))", output)

    def test_visit_wedge_global_var_bounds(self):
        self.setUp()
        self.lv.global_vars = {"x": 1, "y": 3}
        output = self.lv.parse("\\bigwedge_{i=x}^{y}(x_i\landy_i\land(x=z_i))")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(and(and x_1 y_1 (= x z_1))(and x_2 y_2 (= x z_2)))", output)

    def test_visit_wedge_varint_bounds(self):
        # Using simple global arithmetic
        self.setUp()
        self.lv.global_vars = {"x": 1, "y": 3}
        output = self.lv.parse("\\bigwedge_{i=y-2}^{x+2}(x_i\landy_i\land(x=z_i))")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(and(and x_1 y_1 (= x z_1))(and x_2 y_2 (= x z_2)))", output)

    def test_visit_vee(self):
        # Lower and upper variant
        output = self.lv.parse("\\bigvee_{i=1}^{3}(x_i\landy_i\land(x=z_i))")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(or(and x_1 y_1 (= x z_1))(and x_2 y_2 (= x z_2)))", output)

    def test_visit_and(self):
        output = self.lv.parse("(x\landy\landz)")
        self.assertEqual("(and x y z)", output)

        output = self.lv.parse("(x\land(y\landz))")
        self.assertEqual("(and x (and y z))", output)

    def test_visit_or(self):
        output = self.lv.parse("(x\lory)")
        self.assertEqual("(or x y)", output)

        output = self.lv.parse("(x\lory\lorz)")
        self.assertEqual("(or x y z)", output)

    def test_visit_equals(self):
        output = self.lv.parse("(x=y)")
        self.assertEqual("(= x y)", output)

        output = self.lv.parse("(x=y=z)")
        self.assertEqual("(= x y z)", output)

    def test_visit_rexpr(self):
        output = self.lv.parse("(x=y)")
        self.assertEqual("(= x y)", output)

    def test_visit_equals_and_and(self):
        output = self.lv.parse("((x=y)\landx\land(y=z))")
        self.assertEqual("(and (= x y) x (= y z))", output)

    def test_visit_vee_and_wedge(self):
        output = self.lv.parse("\\bigwedge_{i=1}^{3}\\bigvee_{j=0}^{2}(x_i\landy_i\landj\land(x=z_i=j_j=g_j))")
        output = output.replace("\n", "").replace("\r\n", "")
        self.assertEqual("(and(or(and x_1 y_1 j (= x z_1 j_0 g_0))(and x_1 y_1 j (= x z_1 j_1 g_1)))(or(and x_2 y_2 j (= x z_2 j_0 g_0))(and x_2 y_2 j (= x z_2 j_1 g_1))))", output)