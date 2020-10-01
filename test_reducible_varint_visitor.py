from unittest import TestCase

from latex_to_smt import ReducibleVarintVisitor


class TestReducibleVarintVisitor(TestCase):
    def setUp(self):
        self.trvv = ReducibleVarintVisitor({"x": 1, "y": 5, "long": -3})

    def test_visit_varint_int(self):
        output = self.trvv.parse("1")
        self.assertEqual("1", output)

    def test_visit_varint_real(self):
        output = self.trvv.parse("1+0.1")
        self.assertEqual("1.1", output)


    def test_visit_varint_var(self):
        output = self.trvv.parse("x")
        self.assertEqual("1", output)

    def test_visit_long_varint(self):
        output = self.trvv.parse("long")
        self.assertEqual("-3", output)

    def test_visit_varint_combined(self):
        output = self.trvv.parse("x+y-1+long")
        self.assertEqual("2", output)

