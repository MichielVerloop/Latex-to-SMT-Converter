from unittest import TestCase

from latex_to_smt import GlobalVisitor


class TestGlobalVisitor(TestCase):
    def setUp(self):
        self.gv = GlobalVisitor()

    def test_equals(self):
        output = self.gv.parse("x=1+1-1")
        self.assertEqual({"x": 1}, output)

    def test_assignments(self):
        output = self.gv.parse("x=1+1-1,y=x+3")
        self.assertEqual({"x": 1, "y": 4}, output)

    #TODO: test cases for failures
