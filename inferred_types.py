from functools import reduce

unknown = None
num = "Num"
real = "Real"
boolean = "Bool"


def is_num(a):
    return a == real or a == num


def compare_types(a, b):
    # Happy flow: They are equal or one of them is unknown.
    if a or b == b or a:
        return a or b
    # Happy flow: num and real or real and num, but not both are real.
    if is_num(a) and is_num(b):
        return num

    # Exception: they are not comparable types:
    raise ValueError("Types '" + a + "' and '" + b + "' are incomparable.")


def strictest_types(arr):
    return reduce(compare_types, arr)

