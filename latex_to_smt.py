from collections import OrderedDict
from inferred_types import *
from parsimonious.nodes import NodeVisitor
import re  # Less powerful but default regex engine, with regex highlighting
import regex  # Used for special settings, but loses nice regex highlighting

from grammar import BoolGrammar


def main():
    global_vars = get_globals(input("Please enter your globals here:\n"))
    inp = input("formula here:\n")
    result = convert(inp, global_vars, "Int", "Int")
    print(result)


def clean(inp):
    inp = inp.replace(" ", "")
    inp = inp.replace("\\,", "")
    inp = inp.replace("&", "")
    inp = inp.replace("\\\\", "")
    inp = inp.replace("\\_", "")
    return inp


def convert(inp, global_vars, num_type, default_type):
    inp = clean(inp)
    result = ""
    lv = LatexVisitor(global_vars)
    lv.num_type = num_type
    lv.default_type = default_type
    parsed = lv.parse(inp)
    result += lv.get_definitions()
    result += lv.get_globals()
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


def reduce(floats):
    # Takes a list of an even length of the form [operator, num, operator, num, etc.] and computes the result.
    if len(floats) == 0:
        return 0

    result = 0
    while len(floats) != 0:
        shortened = 0
        # TODO: Figure out how to nicely rethrow an error from a failed int(var)
        operator = floats[0]
        num = floats[1]
        result += num if operator == "+" else -num
        floats = floats[2:]
    return result


def resolve(known_vars, varint):
    if len(varint) == 1 or len(varint[0]) == 1:  # Ensure the first argument has an operator.
        varint[0] = ["+", varint[0]]
    # Replace variables with their integer value if possible.
    vars_ = ""
    nums = []
    for i in range(len(varint)):
        sub_var = varint[i][1]
        if sub_var in known_vars:
            replacevar = str(known_vars.get(sub_var))
            hasminus = replacevar[0] == "-"
            if hasminus:
                if varint[i][0] == "+":
                    varint[i] = ["-", replacevar[1:]]
                else:
                    varint[i][1] = replacevar[1:]
            else:
                varint[i][1] = replacevar
        if re.match("[+-]*([0-9]+\\.)?[0-9]+", str(varint[i][1])):
            nums += (varint[i][0], float(varint[i][1]))
        else:
            vars_ += varint[i][0] + str(varint[i][1])
    if nums == "":
        if len(vars_) > 0 and vars_[0] == "+":
            vars_ = vars_[1:]
        return vars_
    reduced_num = reduce(nums)
    # Handle small formatting crap
    if int(reduced_num) == reduced_num:
        reduced_num = str(int(reduced_num))
    else:
        reduced_num = str(reduced_num)

    if len(vars_) > 0:
        if vars_[0] == "+":
            vars_ = vars_[1:]
        if not reduced_num[0] == "-":
            reduced_num = "+" + reduced_num
        if reduced_num == "+0":
            reduced_num = ""
    return vars_ + reduced_num


def check_inequalities(inequalities: [str], assigned_vars: {str, int}) -> bool:
    # Substitute the dictionary into the inequalities
    inequalities = [assigned_vars[eq] if eq in assigned_vars else eq for eq in inequalities]

    # Solve the inequalities
    for i in range(len(inequalities))[1::2]:
        if inequalities[i] == '\\leq' and not int(inequalities[i-1]) <= int(inequalities[i+1]):
            return False
        elif inequalities[i] == '<' and not int(inequalities[i-1]) < int(inequalities[i+1]):
            return False
        elif not inequalities[i] == '\\leq' and not inequalities[i] == '<':
            raise ValueError("Illegal inequality. Expected \\leq or < but got '" + str(inequalities[i]) + "'.")
    return True


def solve_inequalities(inequalities: [str], all_vars: [str], current_var: str,
                       assigned_vars: {str, int}, current_included: bool) -> {str, int}:
    for var in all_vars[all_vars.index(current_var) + (0 if current_included else 1):]:
        in_between = inequalities[inequalities.index(var) - 1]
        old_var = inequalities[inequalities.index(var) - 2]
        if old_var in assigned_vars:
            old_var = assigned_vars[old_var]
        assigned_vars.update({var: int(old_var) + 1 if in_between == "<" else int(old_var)})
    return assigned_vars


def inequalities_rec(inequalities: [str], all_vars: [str] = None, current_var: str = None,
                     assigned_vars: {str, int}=None):
    if all_vars is None:  # Generate all_vars from inequalities
        all_vars = [eq for eq in inequalities if not re.match("<|\\\\leq|(-?[0-9]+)", eq)]
    if current_var is None:  # Set current_var to all_vars[0]
        current_var = all_vars[0]
    if assigned_vars is None:  # Set all vars to the lowest var, recursion will take care of the rest
        assigned_vars = {}
        assigned_vars.update(solve_inequalities(inequalities, all_vars, current_var, assigned_vars,
                                                current_included=True))
    # Base case inequalities not satisfied and final var is reached
    if not check_inequalities(inequalities, assigned_vars) and current_var == all_vars[-1]:
        return

    # Base case last var: actual yields go here.
    if current_var == all_vars[-1]:
        # dict() is to yield the copy of the array so no shenanigans happen.
        yield dict(assigned_vars)

    # Recursive case

    # Go to the next variable if possible.
    if not current_var == all_vars[-1]:
        yield from inequalities_rec(inequalities, all_vars, all_vars[all_vars.index(current_var) + 1], assigned_vars)
    # Increment the current variable and determine the lowest possible values for all subsequent variables
    assigned_vars.update({current_var: assigned_vars[current_var] + 1})
    assigned_vars.update(solve_inequalities(inequalities, all_vars, current_var, assigned_vars, current_included=False))
    # If the inequalities still hold true, make a recursive call, else return
    if check_inequalities(inequalities, assigned_vars):
        yield from inequalities_rec(inequalities, all_vars, current_var, assigned_vars)


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
        # If there is nothing before the dot, prepend a 0.
        if node.text.find(".") == 0:
            return "0" + node.text
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
        # If there is nothing before the dot, prepend a 0.
        if node.text.find(".") == 0:
            return "0" + node.text
        return node.text

    def generic_visit(self, node, visited_children):
        # result = ""
        # for child in visited_children:
        #     result += str(child)
        return visited_children or node.text


class LatexVisitor(NodeVisitor):

    def __init__(self, global_vars):
        self.variables = OrderedDict()
        self.global_vars = global_vars
        self.grammar = BoolGrammar.latex_grammar
        self.default_type = "Int"
        self.num_type = "Int"

    def parse(self, text, pos=0, hide_type=True):
        if hide_type:  # We only want the parsed string
            return super().parse(text, pos)[0]
        else:  # We also want the type
            return super().parse(text, pos)

    def __update_type__(self, potential_var, arg_type):
        if arg_type == unknown:
            return  # Default; type would already be set to this.
        if not re.match("[a-z]+(_{[a-z](,[a-z]+)+_})?", potential_var):
            return
        if self.variables.get(potential_var) is not None \
                and not arg_type == self.variables.get(potential_var):
            raise ValueError("Type " + str(self.variables.get(potential_var)) + " was inferred but type "
                             + arg_type + " was also inferred for variable " + potential_var + ".")
        if potential_var in self.variables and self.variables.get(potential_var) is None:
            self.variables.update({potential_var: arg_type})

    def __substitute_dict__(self, expr, dic):
        for key in dic:
            expr = self.__substitute__(expr, key, dic[key])
        return expr

    def __substitute__(self, expr, localvar, value):
        # Copy dict and add localvar:value to it.
        known_vars = self.global_vars.copy()
        known_vars.update({localvar: value})
        # Match all subvars

        it = regex.finditer("_([a-z0-9]+([+-][a-z0-9]+)*)([_)\n ]|$)", expr, re.IGNORECASE, overlapped=True)

        # Split up all subvars so they can be resolved by resolve.
        locations = []
        reduced_vars = []
        for i in it:
            location = i.span()
            front = "_"
            subvar, _, end = i.groups()
            subvar = re.split("([+-])", subvar)
            subvar = [subvar[0]] + [subvar[1:][j * 2:j * 2 + 2] for j in range(int(len(subvar[1:]) / 2))]
            locations.append(location)
            middle = resolve(known_vars, subvar)
            reduced_vars.append(front + middle + end)
        # In reverse (so locations stay relevant), replace the parts of the string where necessary.
        assert len(locations) == len(reduced_vars)
        for i in range(len(locations))[::-1]:
            expr = expr[:locations[i][0]] + reduced_vars[i] + expr[locations[i][1]:]
        # Edge case that doesn't need all the crap above.
        expr = expr.replace("\\markreplaceable{" + localvar + "}", str(value))
        return expr

    def get_definitions(self):
        result = ""
        for var in self.global_vars:
            self.variables.update({var: "Num"})
        for var in self.variables:
            var_type = self.variables.get(var)
            if var_type == "Num":
                var_type = self.num_type
            if var_type is None:
                var_type = self.default_type
            result += "(declare-const " + var + " " + var_type + ")\n"
        return result

    def get_globals(self):
        result = ""
        for i in self.global_vars:
            result += "(assert (= " + i + " " + str(self.global_vars.get(i)) + "))\n"
        return result

    def handle_sums(self, operand, visited_children):
        # _, (localvar, localvarstart), _, _, localvarend, (expr, typ) = visited_children
        # print(localvar + str(localvarstart))
        localvar = visited_children[1][0]
        localvarstart = int(visited_children[1][1])
        localvarend = int(visited_children[4])
        expr, typ = visited_children[6]
        return self.handle_sum(operand, localvar, localvarstart, localvarend, expr),\
               BoolGrammar.inverse_operand_dict.get(operand)[2]

    def handle_sum(self, operand, localvar, localvarstart, localvarend, expr):
        known_operand = operand in BoolGrammar.inverse_operand_dict
        if known_operand:
            operand = BoolGrammar.inverse_operand_dict.get(operand)[0]
        result = ""
        if known_operand:  # No need to add an operand or braces if the operands repeat.
            result += "(" + operand

        # substitute the variable in the expression
        for i in range(localvarstart, localvarend):
            result += "\n" + self.__substitute__(expr, localvar, i)
        # Replace the general version of the variables with the non-general version
        localsetvars = OrderedDict()
        for var in self.variables:
            # It is okay for this not to match on _ + localvar + _ as __substitute__ doesn't wrongly replace variables.
            if "_" + localvar in var:
                localsetvars.update({var: self.variables.get(var)})
        for var in localsetvars:
            self.variables.pop(var)  # Wrongly deleted x_ii if x_i is matched, but x_ii is added to the back again.
            for i in range(localvarstart, localvarend):
                newvar = self.__substitute__(var, localvar, i)
                self.variables.update({newvar: localsetvars.get(var)})
        if known_operand:  # Only add ending brackets if we added an operand
            result += ")"
        else:  # We do not need an extra enter
            result = result.rstrip()
        return result

    def handle_rsum(self, operand, visited_children):
        operand, arg_type, res_type = BoolGrammar.inverse_operand_dict.get(operand)
        localvars = visited_children[1][0]
        minimum = visited_children[1][1][0]
        maximum = visited_children[1][3][0]
        inequalities = [minimum] + visited_children[1][2] + [maximum]
        expr, typ = visited_children[3]

        # Check for variables in the inequalities that are not in the local variables
        remaining_vars = [x for x in inequalities if x not in localvars and not re.match("<|\\\\leq|(-?[0-9]+)", x)]
        if len(remaining_vars) != 0:
            raise ValueError("Found variable(s) " + str(remaining_vars) + " in the inequalities " + str(inequalities)
                             + " that were not introduced in the local variables, " + str(localvars) + ".")
        # Conversely, check for variables in the local variables that are not in the inequalities
        remaining_vars = [x for x in localvars if x not in inequalities]
        if len(remaining_vars) != 0:
            raise ValueError("Found variable(s) " + str(remaining_vars) + " in the local variables " + str(localvars)
                             + " that were not introduced in the inequalities, " + str(inequalities) + ".")

        # Generate the rest of the expression
        result = "(" + operand +\
               ''.join("\n" + self.__substitute_dict__(expr, dic) for dic in inequalities_rec(inequalities)) + ")"

        # Update self.variables
        localsetvars = OrderedDict()
        for var in self.variables:
            # It is okay for this not to match on _ + localvar + _ as __substitute__ doesn't wrongly replace variables.
            for localvar in localvars:
                if "_" + localvar in var:
                    localsetvars.update({var: self.variables.get(var)})
        for var in localsetvars:
            self.variables.pop(var)  # Wrongly deleted x_ii if x_i is matched, but x_ii is added to the back again.
            for dic in inequalities_rec(inequalities):
                newvar = self.__substitute_dict__(var, dic)
                self.variables.update({newvar: localsetvars.get(var)})

        # expr = "(=> " + crap + " " + expr + ")"
        # # The vars with the lowest length are generated first, so the "i" doesn't replace the i in "xi"
        # for var in sorted(localvars, key=len, reverse=True):
        #     if var not in inequalities:
        #         raise ValueError("Var " + var + " was not found in " + str(inequalities))
        #     expr = self.handle_sum("", var, truemin(var, inequalities, minimum),
        #                            truemax(var, inequalities, maximum) + 1,  # + 1 is to compensate for the exclusivity
        #                            expr)  # of the upper bound
        return result, res_type

    def visit_reduciblevarint(self, _, visited_children):
        strung_together = visited_children[0][0]
        if not (len(visited_children) == 2 and visited_children[1] == ''):
            for operand, (varint, _) in visited_children[1:]:
                strung_together += str(operand) + str(varint)
        result = ReducibleVarintVisitor(self.global_vars).parse(strung_together)
        return str(result)

    def visit_var(self, node, visited_children):
        var = node.text.replace(",", "_").replace("{", "").replace("}", "")
        if var not in self.variables:
            self.variables.update({var: None})
        return var, unknown

    def visit_int(self, node, _):
        # If there is nothing before the dot, prepend a 0.
        if node.text.find(".") == 0:
            return "0" + node.text, real
        return node.text, real if "." in node.text else num

    def visit_varint(self, _, visited_children):
        return visited_children[0]

    def visit_replaceablevar(self, _, visited_children):
        markreplaceable, (expr, typ), rbrace = visited_children
        self.variables.pop(expr)
        return markreplaceable + expr + rbrace, typ

    def visit_localvars(self, _, visited_children):
        if "" in visited_children[1]:  # Case only 1 localvar
            visited_children.remove("")
            result = [visited_children[0]]
        else:
            if isinstance(visited_children[1][1], str):  # Case 2 local vars, bleeds into 3+ cases
                visited_children[1] = [visited_children[1]]
            # Case 3+ local vars
            result = [visited_children[0]] + [i[1] for i in visited_children[1]]
        return result

    def visit_expr(self, _, visited_children):
        return visited_children[0]

    def visit_nexpr(self, _, visited_children):
        lbracket, (lexpr, ltype), rexpr, rbracket = visited_children
        operand, arg_type, res_type = BoolGrammar.inverse_operand_dict.get(rexpr[0][0])
        # If the type of the arguments cannot be inferred from the operator, check whether any of the arguments
        # have a type that can be used.
        arg_type = arg_type or strictest_types([ltype] + [rtype for _, (_, rtype) in rexpr])
        # Then, update the types using arg_type for all arguments:
        [self.__update_type__(subexpr, arg_type) for _, (subexpr, _) in rexpr]
        self.__update_type__(lexpr, arg_type)

        # Create the resulting expression
        expr = operand + " " + lexpr + "".join([" " + subexpr for _, (subexpr, _) in rexpr])
        result = lbracket + expr + rbracket
        return result, res_type

    def visit_lower(self, _, visited_children):
        return [visited_children[0], visited_children[2]]

    def visit_lowup(self, _, visited_children):
        localvars = visited_children[0]
        minimum = [visited_children[2]]
        inequalities = [visited_children[3]] + [i for j in visited_children[4] for i in j]  # Flatten
        maximum = [visited_children[5]]
        return [localvars] + [minimum] + [inequalities] + [maximum]

    def visit_ite(self, _, visited_children):
        _, condition, _, then, _, else_ = visited_children
        return "(ite " + condition[0] + " " + then[0] + " " + else_[0] + ")", strictest_types([then[1], else_[1]])

    def visit_wedge(self, _, visited_children):
        return self.handle_sums("\\bigwedge", visited_children)

    def visit_vee(self, _, visited_children):
        return self.handle_sums("\\bigvee", visited_children)

    def visit_sum(self, _, visited_children):
        return self.handle_sums("\\sum", visited_children)

    def visit_rwedge(self, _, visited_children):
        return self.handle_rsum("\\bigwedge", visited_children)

    def visit_rvee(self, _, visited_children):
        return self.handle_rsum("\\bigvee", visited_children)

    def visit_rsum(self, _, visited_children):
        return self.handle_rsum("\\sum", visited_children)

    def visit_not(self, _, visited_children):
        operand, (subexpr, _) = visited_children
        self.__update_type__(subexpr, boolean)
        return "(not " + subexpr + ")", boolean

    def visit_neq(self, _, visited_children):
        return visited_children

    def visit_and(self, _, visited_children):
        return visited_children

    def visit_or(self, _, visited_children):
        return visited_children

    def visit_implies(self, _, visited_children):
        return visited_children

    def visit_equals(self, _, visited_children):
        return visited_children

    def visit_le(self, _, visited_children):
        return visited_children

    def visit_leq(self, _, visited_children):
        return visited_children

    def visit_ge(self, _, visited_children):
        return visited_children

    def visit_geq(self, _, visited_children):
        return visited_children

    def visit_plus(self, _, visited_children):
        return visited_children

    def visit_minus(self, _, visited_children):
        return visited_children

    def visit_times(self, _, visited_children):
        return visited_children

    def generic_visit(self, node, visited_children):
        if isinstance(visited_children, list) and len(visited_children) == 1:
            # Gets rid of excessive list encapsulation, but introduces boilerplat code for many operands.
            return visited_children[0]
        return visited_children or node.text


if __name__ == '__main__':
    main()
