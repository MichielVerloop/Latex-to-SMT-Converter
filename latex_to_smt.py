from parsimonious.nodes import NodeVisitor

from OrderedSet import OrderedSet
from grammar import BoolGrammar


def main():
    inp = input("formula here:\n")
    inp = clean(inp)
    result = convert(inp)
    print(result)


def clean(inp):
    inp = inp.replace(" ", "")
    inp = inp.replace("\\,", "")
    inp = inp.replace("&", "")
    inp = inp.replace("\\\\", "")
    return inp


def convert(inp):
    result = ""
    iv = IniVisitor()
    parsed = iv.parse(inp)
    result += iv.get_definitions()
    result += "(assert\n"
    result += parsed
    result += ")\n(check-sat)\n(get-model)"
    return result


class IniVisitor(NodeVisitor):

    def __init__(self):
        self.variables = OrderedSet([])
        self.result = []
        self.grammar = BoolGrammar.grammar

    def get_definitions(self):
        result = ""
        for var in self.variables:
            result += "(declare-const " + var + " Int)\n"
        return result

    def handle_rexpr(self, operand, visited_children):
        result = ""
        for child in visited_children:
            result += child.replace(BoolGrammar.operand_dict.get(operand), " ")
        return [operand + " ", result]

    def handle_sum(self, operand, visited_children):
        result = "(" + operand + "\n"
        #TODO: case lowup

        # case lower and upper
        localvar = visited_children[1][0]
        localvarstart = int(visited_children[1][1])
        localvarend = int(visited_children[4])
        expr = visited_children[6]

        # substitute the variable in the expression
        for i in range(localvarstart, localvarend):
            result += expr.replace("_" + localvar, "_" + str(i)) + "\n"

        # Replace the general version of the variables with the non-general version
        localsetvars = OrderedSet([])
        for var in self.variables:
            if "_" + localvar in var:
                localsetvars.add(var)
        for var in localsetvars:
            self.variables.remove(var)
            for i in range(localvarstart, localvarend):
                self.variables.add(var.replace("_" + localvar, "_" + str(i)))

        result += ")"
        return result

    def visit_var(self, node, visited_children):
        self.variables.add(node.text)
        return node.text

    def visit_local_var(self, node, visited_children):
        return node.text

    def visit_expr(self, node, visited_children):
        return visited_children[0]

    def visit_nexpr(self, node, visited_children):
        lbracket, lexpr, rexpr, rbracket = visited_children
        result = lbracket + str(rexpr[0]) + lexpr + str(rexpr[1]) + rbracket
        return result

    def visit_rexpr(self, node, visited_children):
        return visited_children[0]

    def visit_lower(self, node, visited_children):
        return [visited_children[0],  visited_children[2]]

    def visit_wedge(self, node, visited_children):
        return self.handle_sum("and", visited_children)

    def visit_vee(self, node, visited_children):
        return self.handle_sum("or", visited_children)

    def visit_not(self, node, visited_children):
        return self.handle_rexpr("not", visited_children)

    def visit_and(self, node, visited_children):
        return self.handle_rexpr("and", visited_children)

    def visit_or(self, node, visited_children):
        return self.handle_rexpr("or", visited_children)

    def visit_implies(self, node, visited_children):
        return self.handle_rexpr("=>", visited_children)

    def visit_equals(self, node, visited_children):
        return self.handle_rexpr("=", visited_children)

    def visit_le(self, node, visited_children):
        return self.handle_rexpr("<", visited_children)

    def visit_leq(self, node, visited_children):
        return self.handle_rexpr("<=", visited_children)

    def visit_ge(self, node, visited_children):
        return self.handle_rexpr(">", visited_children)

    def visit_geq(self, node, visited_children):
        return self.handle_rexpr(">=", visited_children)

    def generic_visit(self, node, visited_children):
        result = ""
        for child in visited_children:
            result += str(child)
        return result or node.text


if __name__ == '__main__':
    main()
