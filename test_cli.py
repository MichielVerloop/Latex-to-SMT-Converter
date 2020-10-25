from unittest import TestCase

from click.testing import CliRunner

from cli import handle_cli


class TestCli(TestCase):
    def setUp(self):
        self.runner = CliRunner()

    def test_handle_cli_no_args(self):
        # Should throw a type error as the required argument 'formula' is not given.
        self.assertRaisesRegex(ValueError, "Argument 'formula' should not be empty.",
                               self.runner.invoke, handle_cli, [""], None, None, False)

    def test_handle_cli_no_globals(self):
        result = self.runner.invoke(handle_cli, ["\\bigwedge_{i:0<i<2}(x_i = 1)"])
        self.assertEqual(0, result.exit_code)
        self.assertEqual("(declare-const x_1 Int)\n(assert\n(and\n(= x_1 1)))\n(check-sat)\n("
                         "get-model)\n",
                         result.output)

    def test_handle_cli_globals(self):
        result = self.runner.invoke(handle_cli, ["\\bigwedge_{i:0<i<R}(x_i = 1)", "-g", "R = 2"])
        self.assertEqual(0, result.exit_code)
        self.assertEqual("(declare-const R Int)\n(declare-const x_1 Int)\n(assert (= R 2))\n(assert\n(and\n(= x_1 1)))"
                         "\n(check-sat)\n(get-model)\n",
                         result.output)

    def test_handle_cli_num_type(self):
        result = self.runner.invoke(handle_cli, ["(x + y)", "-n", "Real"])
        self.assertEqual(0, result.exit_code)
        self.assertIn("Real", result.output)

    def test_handle_cli_default_type(self):
        result = self.runner.invoke(handle_cli, ["(x = y)", "-d", "Bool"])
        self.assertEqual(0, result.exit_code)
        self.assertIn("Bool", result.output)
