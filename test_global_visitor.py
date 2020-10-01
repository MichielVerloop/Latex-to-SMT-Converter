from unittest import TestCase

from latex_to_smt import GlobalVisitor


class TestGlobalVisitor(TestCase):
    def setUp(self):
        self.gv = GlobalVisitor()

    def test_equals(self):
        output = self.gv.parse("x=1+1-1")
        self.assertEqual({"x": "1"}, output)

    def test_assignments(self):
        output = self.gv.parse("x=1+1-1,y=x+3")
        self.assertEqual({"x": "1", "y": "4"}, output)

    def test_underscores(self):
        output = self.gv.parse("abcidjk_0=11")
        self.assertEqual({"abcidjk_0": "11"}, output)

    def test_unknowns(self):
        output = self.gv.parse("x=y+1-1")
        self.assertEqual({"x": "y"}, output)

        self.setUp()
        output = self.gv.parse("x=0-y+1-1-1")
        self.assertEqual({"x": "-y-1"}, output)

    #TODO: test cases for failures
