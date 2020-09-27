from parsimonious.nodes import NodeVisitor
import re

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


def truemin(var, inequalities, minimum):
    for i in inequalities:
        if i == "<":
            minimum += 1
        if i == var:
            break
    return minimum


def truemax(var, inequalities, maximum):
    for i in inequalities[::-1]:  # reverse the list
        if i == "<":
            maximum -= 1
        if i == var:
            break
    return maximum


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
            replacelimit = child.find("(")
            if replacelimit == -1:
                result += child.replace(BoolGrammar.operand_dict.get(operand), " ")
            else:
                result += child[0:replacelimit].replace(BoolGrammar.operand_dict.get(operand), " ") \
                      + child[replacelimit:]
        return [operand + " ", result]

    def handle_sums(self, operand, visited_children):
        localvar = visited_children[1][0]
        localvarstart = int(visited_children[1][1])
        localvarend = int(visited_children[4])
        expr = visited_children[6]
        return self.handle_sum(operand, localvar, localvarstart, localvarend, expr)

    def handle_sum(self, operand, localvar, localvarstart, localvarend, expr):
        add_operand = operand != ""
        result = ""
        if add_operand:  # Only add an operand if we have an operand to add
            result += "(" + operand + "\n"
        # TODO: case lowup
        # substitute the variable in the expression
        for i in range(localvarstart, localvarend):
            # Because we match on adjacent underscores, we need to do two passes.
            # Only in the second one we add it to the result
            subresult = expr.replace("_" + localvar + "_", "_" + str(i) + "_") \
                .replace("_" + localvar + "\n", "_" + str(i) + "\n") \
                .replace("_" + localvar + " ", "_" + str(i) + " ") \
                .replace("_" + localvar + ")", "_" + str(i) + ")") \
                .replace("\\markreplaceable{" + localvar + "}", str(i))
            result += subresult.replace("_" + localvar + "_", "_" + str(i) + "_") \
                .replace("_" + localvar + "\n", "_" + str(i) + "\n") \
                .replace("_" + localvar + " ", "_" + str(i) + " ") \
                .replace("_" + localvar + ")", "_" + str(i) + ")")
            # Find variables at the end of the string and replace them
            if result.rfind("_" + localvar) + len("_" + localvar) == len(result):
                result = result[0:result.rfind("_" + localvar) + 1] + str(i)
            result += "\n"
        # Replace the general version of the variables with the non-general version
        localsetvars = OrderedSet([])
        for var in self.variables:
            if "_" + localvar in var:
                localsetvars.add(var)
        for var in localsetvars:
            self.variables.remove(var)
            for i in range(localvarstart, localvarend):
                self.variables.add(var.replace("_" + localvar, "_" + str(i)))
        if add_operand:  # Only add ending brackets if we added an operand
            result += ")"
        else:  # We do not need an extra enter
            result = result.rstrip()
        return result

    def handle_rsum(self, operand, visited_children):
        localvars = visited_children[1][0]
        minimum = int(visited_children[1][1][0])
        inequalities = visited_children[1][2]
        maximum = int(visited_children[1][3][0])
        expr = visited_children[3]
        # The vars with the lowest length are generated first, so the "i" doesn't replace the i in "xi"
        for var in sorted(localvars, key=len, reverse=True):
            if not var in inequalities:
                raise ValueError("Var " + var + " was not found in " + str(inequalities))
            expr = self.handle_sum("", var, truemin(var, inequalities, minimum),
                                   truemax(var, inequalities, maximum) + 1,  # + 1 is to compensate for the exclusivity
                                   expr)  # of the upper bound
        remaining_vars = [x for x in inequalities if x not in localvars + ["\\leq"] + ["<"]]
        if len(remaining_vars) != 0:
            raise ValueError("Found variable(s) " + str(remaining_vars) + " in the inequalities " + str(inequalities)
                             + "that were not introduced in the local variables, " + str(localvars) + ".")
        result = "(" + operand + "\n" + expr + ")"
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

    def visit_replaceablevar(self, node, visited_children):
        self.variables.remove(visited_children[1])
        return visited_children[0] + visited_children[1] + visited_children[2]
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

    def visit_lowup(self, node, visited_children):
        localvars = [visited_children[0]] + visited_children[1].split(",")
        localvars.remove("")
        minimum = [visited_children[3]]
        inequalities = [visited_children[4]] + re.split("(\\\\leq|<)", visited_children[5])
        inequalities.remove("")
        maximum = [visited_children[6]]
        return [localvars] + [minimum] + [inequalities] + [maximum]

    def visit_ite(self, node, visited_children):
        return "(ite " + visited_children[1] + " " + visited_children[3] + " " + visited_children[5] + ")"

    def visit_wedge(self, node, visited_children):
        return self.handle_sums("and", visited_children)

    def visit_vee(self, node, visited_children):
        return self.handle_sums("or", visited_children)

    def visit_sum(self, node, visited_children):
        return self.handle_sums("+", visited_children)

    def visit_rwedge(self, node, visited_children):
        return self.handle_rsum("and", visited_children)

    def visit_rvee(self, node, visited_children):
        return self.handle_rsum("or", visited_children)

    def visit_rsum(self, node, visited_children):
        return self.handle_rsum("+", visited_children)

    def visit_not(self, node, visited_children):
        return "(not " + visited_children[1] + ")"

    def visit_neq(self, node, visited_children):
        return self.handle_rexpr("distinct", visited_children)

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
