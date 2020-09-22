from parsimonious.nodes import NodeVisitor
from six import reraise

from OrderedSet import OrderedSet
from grammar import BoolGrammar


def main():
    global_vars = get_globals(input("Please enter your globals here:\n"))
    inp = input("formula here:\n")
    result = convert(inp, global_vars)
    print(result)


def clean(inp):
    inp = inp.replace(" ", "")
    inp = inp.replace("\\,", "")
    inp = inp.replace("&", "")
    inp = inp.replace("\\\\", "")
    return inp


def convert(inp, global_vars):
    inp = clean(inp)
    result = ""
    lv = LatexVisitor(global_vars)
    parsed = lv.parse(inp)
    result += lv.get_definitions()
    result += "(assert\n"
    result += parsed
    result += ")\n(check-sat)\n(get-model)"
    return result


def get_globals(inp):
    inp = clean(inp)
    if inp == "":
        return {}
    gv = GlobalVisitor()
    globs = gv.parse(inp)
    return globs


def flatten(l):
    return [item for sublist in l for item in sublist]


def resolve_global_or_int(global_vars, varint):
    if varint in global_vars:
        return global_vars.get(varint)
    try:
        return int(varint)
    except ValueError:
        return float(varint)


def resolve(global_vars, varint):
    if len(varint) == 1:
        return resolve_global_or_int(global_vars, varint[0])
    new_varint = [varint[0]]
    for i in range(1, len(varint)):
        new_varint += [varint[i][0]] + [varint[i][1]]
    varint = new_varint
    # else
    while len(varint) != 1:
        shortened = 0
        # TODO: Figure out how to nicely rethrow an error from a failed int(var)
        int1 = resolve_global_or_int(global_vars, varint[0])
        int2 = resolve_global_or_int(global_vars, varint[2])
        if varint[1] == "+":
            shortened = int1 + int2
        elif varint[1] == "-":
            shortened = int1 - int2

        del varint[0]
        del varint[0]
        varint[0] = shortened
    return varint[0]


class GlobalVisitor(NodeVisitor):
    # Not beautiful, but it works
    def __init__(self):
        self.global_vars = {}
        self.grammar = BoolGrammar.global_grammar
        self.unwrapped_exceptions = ValueError

    def visit_assignments(self, node, visited_children):
        return self.global_vars

    def visit_equals(self, node, visited_children):
        var = visited_children[0]
        result = visited_children[2]
        self.global_vars[var] = result
        return visited_children

    def visit_pmvarint(self, node, visited_children):
        return flatten(visited_children)

    def visit_varint(self, node, visited_children):
        visited_children = flatten(visited_children)
        return resolve(self.global_vars, visited_children)

    def visit_var(self, node, visited_children):
        return node.text

    def visit_int(self, node, visited_children):
        return node.text

    def generic_visit(self, node, visited_children):
        return visited_children or node.text


class ReducibleVarintVisitor(NodeVisitor):
    def __init__(self, global_vars):
        self.global_vars = global_vars
        self.grammar = BoolGrammar.reducible_varint_grammar

    def visit_pmvarint(self, node, visited_children):
        return flatten(visited_children)

    def visit_varint(self, node, visited_children):
        visited_children = flatten(visited_children)
        return resolve(self.global_vars, visited_children)

    def visit_var(self, node, visited_children):
        return node.text

    def visit_int(self, node, visited_children):
        return node.text

    def generic_visit(self, node, visited_children):
        # result = ""
        # for child in visited_children:
        #     result += str(child)
        return visited_children or node.text


class LatexVisitor(NodeVisitor):

    def __init__(self, global_vars):
        self.variables = OrderedSet([])
        self.global_vars = global_vars
        self.grammar = BoolGrammar.latex_grammar

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
        # TODO: case lowup
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

    def visit_reduciblevarint(self, node, visited_children):
        strung_together = ""
        for child in visited_children:
            strung_together += str(child)
        result = ReducibleVarintVisitor(self.global_vars).parse(strung_together)
        return str(result)

    def visit_var(self, node, visited_children):
        var = node.text.replace(",", "_").replace("{", "").replace("}", "")
        self.variables.add(var)
        return var

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
        return [visited_children[0], visited_children[2]]

    def visit_wedge(self, node, visited_children):
        return self.handle_sum("and", visited_children)

    def visit_vee(self, node, visited_children):
        return self.handle_sum("or", visited_children)

    def visit_sum(self, node, visited_children):
        return self.handle_sum("+", visited_children)

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

    def visit_plus(self, node, visited_children):
        return self.handle_rexpr("+", visited_children)

    def visit_minus(self, node, visited_children):
        return self.handle_rexpr("-", visited_children)

    def visit_times(self, node, visited_children):
        return self.handle_rexpr("*", visited_children)

    def generic_visit(self, node, visited_children):
        result = ""
        for child in visited_children:
            result += str(child)
        return result or node.text


if __name__ == '__main__':
    main()
