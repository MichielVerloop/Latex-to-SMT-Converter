from parsimonious.grammar import Grammar


class BoolGrammar:
    grammar = Grammar(
        """
    expr      = wedge / vee / varint / nexpr
    nexpr     = "("expr rexpr")"
    rexpr     = not / and / or / implies / equals / le / leq / ge / geq / varint
    wedge     = ("\\\\bigwedge_{" lower "}" "^{" varint "}" expr)
    vee       = ("\\\\bigvee_{" lower "}" "^{" varint "}" expr)
    lower     = localvar "=" varint
    lowup     = localvar (","localvar)* ":" varint (("\\\\leq" / "<") varint)+
    varint    = (var / int) (("+" / "-") (var / int))*
    int       = ~"[0-9]"+
    localvar  = ~"[a-z_]+"i
    var       = ~"[a-z_]+"i
    and       = ("\\\\land" expr)+
    or        = ("\\\\lor" expr)+
    implies   = ("\\\\to" expr)+
    equals    = ("=" expr)+
    not       = "\\\\lnot" expr
    le        = "<" expr
    leq       = "\\\\leq" expr
    ge        = ">" expr
    geq       = "\\\\geq" expr
    """)

    operand_dict = {
        "not": "\\lnot",
        "and": "\\land",
        "or": "\\lor",
        "=>": "\\to",
        "<=": "\\leq",
        ">=": ">\\geq",
        "=": "=",
        "<": "<",
        ">": ">"
    }
