import re
from parsimonious.grammar import Grammar


# TODO: negative integers
class BoolGrammar:
    latex_grammar = Grammar(
        """
    expr            = wedge / rwedge / vee / rvee / sum / rsum / ite / not / varint / nexpr
    nexpr           = "("expr rexpr")"
    rexpr           = and / or / implies / equals / neq / le / leq / ge / geq / plus / minus / times / varint
    ite             = "\\\\T{if}" expr "\\\\T{then}" expr "\\\\T{else}" expr
    wedge           = "\\\\bigwedge_{" lower "}" "^{" reduciblevarint "}" expr
    vee             = "\\\\bigvee_{" lower "}" "^{" reduciblevarint "}" expr
    rwedge          = "\\\\bigwedge_{" lowup "}" expr
    rvee            = "\\\\bigvee_{" lowup "}" expr
    sum             = "\\\\sum_{" lower "}" "^{" reduciblevarint "}" expr
    rsum            = "\\\\sum_{" lowup "}" expr
    lower           = localvar "=" reduciblevarint
    lowup           = localvar (","localvar)* ":" reduciblevarint ("\\\\leq" / "<") (localvar ("\\\\leq" / "<"))+ reduciblevarint
    reduciblevarint = (var / int) (("+" / "-") (var / int))*
    varint          = (var / replaceablevar / int)
    int             = (~"[0-9]"* ".")? ~"[0-9]"+
    localvar        = ~"[a-z_]+"i
    replaceablevar  = "\\\\markreplaceable{" var "}"
    var             = (string "_{" substring ("," substring)* "}") / (string "_" (string/int)) / (string)
    substring       = (string / int) (("+" / "-") (string / int))* 
    string          = ~"[a-z]+"i
    and             = ("\\\\land" expr)+
    or              = ("\\\\lor" expr)+
    implies         = ("\\\\to" expr)+
    equals          = ("=" expr)+
    neq             = ("\\\\neq" expr)+
    not             = "\\\\lnot" expr
    le              = "<" expr
    leq             = "\\\\leq" expr
    ge              = ">" expr
    geq             = "\\\\geq" expr
    plus            = "+" expr
    minus           = "-" expr
    times           = "\\\\cdot" expr 
    """)

    global_grammar = Grammar(
        """
    assignments     = equals ("," equals)*
    equals          = var "=" varint
    varint          = (var / int) (pmvarint)*
    pmvarint        = ("+" / "-") (var / int)
    var             = (string "_{" substring ("," substring)* "}") / (string "_" (string/int)) / (string)
    substring       = (string / int) (("+" / "-") (string / int))* 
    string          = ~"[a-z]+"i
    int             = (~"[0-9]"* ".")? ~"[0-9]"+  
    """
    )

    # TODO: update this with the "num" definition rather than int.
    reducible_varint_grammar = Grammar(
        """
    varint          = (var / int) (pmvarint)*
    pmvarint        = ("+" / "-") (var / int)
    var             = (string "_{" substring ("," substring)* "}") / (string "_" (string/int)) / (string)
    substring       = (string / int) (("+" / "-") (string / int))* 
    string          = ~"[a-z]+"i
    int             = (~"[0-9]"* ".")? ~"[0-9]"+
    """
    )

    operand_dict = {
        "distinct": ("\\neq", None),
        "=": ("=", None),
        "not": ("\\lnot", "Bool"),
        "and": ("\\land", "Bool"),
        "or": ("\\lor", "Bool"),
        "=>": ("\\to", "Bool"),
        "<=": ("\\leq", "Num"),
        ">=": ("\\geq", "Num"),
        "*": ("\\cdot", "Num"),
        "<": ("<", "Num"),
        ">": (">", "Num"),
        "+": ("+", "Num"),
        "-": ("-", "Num")
    }
