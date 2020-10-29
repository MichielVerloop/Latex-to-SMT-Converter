# Latex to SMT Converter
Converts latex boolean formulas to the smt format used by SAT-solvers such as z3.

# Features
* Converts the LaTeX boolean format to smt while requiring minimal added input from the user.  
* Support for global variables.
* Automatic type inference.
* Support for subscripting variables with simple arithmetic operations
* Ability to internally use global variables.
* Ability to do simple plus and minus operations on known variables and integers.
* Ignores layout characters such as `\&`, `\,`,  `\\` and newline characters.

# Example usages
The source tex `(5 \geq \sum_{i=0}^{n} \T{if}\, (2 = (p_i + p_{i+1})) \,\T{then}\, 1 \,\T{else}\, 0)` produces the below formula in the pdf:  
![Example1](https://i.imgur.com/9yA5mfg.png)  
Using the arguments `cli.py "(5 \geq \sum_{i=0}^{n} \T{if}\, (2 = (p_i + p_{i+1})) \,\T{then}\, 1 \,\T{else}\, 0)" -g n=3`, the tool can convert it to the following smt file:
```
(declare-const n Int)
(declare-const p_0 Int)
(declare-const p_1 Int)
(declare-const p_2 Int)
(declare-const p_3 Int)
(assert (= n 3))
(assert
(>= 5 (+
(ite (= 2 (+ p_0 p_1)) 1 0)
(ite (= 2 (+ p_1 p_2)) 1 0)
(ite (= 2 (+ p_2 p_3)) 1 0))))
(check-sat)
(get-model)
```
This smt format can then be solved using z3, see [this](https://rise4fun.com/Z3/9sxC) for an example solution.

The source tex `\bigwedge_{i,j:0\leq i<j<4} (((\markreplaceable{i} + \markreplaceable{j}) < 5) \to \lnot((x_i + w_i) \geq x_j))` produces the below formula in the pdf:  
![Example2](https://i.imgur.com/rZ0cGGg.png)  
Using the arguments `cli.py "\bigwedge_{i,j:0\leq i<j<4} (((\markreplaceable{i} + \markreplaceable{j}) < 5) \to \lnot((x_i + w_i) \geq x_j))"`, the tool can convert it to the following smt file:
```
(declare-const x_0 Int)
(declare-const x_1 Int)
(declare-const x_2 Int)
(declare-const w_0 Int)
(declare-const w_1 Int)
(declare-const w_2 Int)
(declare-const x_3 Int)
(assert
(and
(=> (< (+ 0 1) 5) (not (>= (+ x_0 w_0) x_1)))
(=> (< (+ 0 2) 5) (not (>= (+ x_0 w_0) x_2)))
(=> (< (+ 0 3) 5) (not (>= (+ x_0 w_0) x_3)))
(=> (< (+ 1 2) 5) (not (>= (+ x_1 w_1) x_2)))
(=> (< (+ 1 3) 5) (not (>= (+ x_1 w_1) x_3)))
(=> (< (+ 2 3) 5) (not (>= (+ x_2 w_2) x_3)))))
(check-sat)
(get-model)
```
This smt format can then be solved using z3, see [this](https://rise4fun.com/Z3/owAXO) for an example solution.
# Limitations
* Brackets are necessary for `and`, `or`, `implies`, `equals`, `not equal`, `less than`, `less than or equal to`, `greater than`, `greater than or equal to`, `plus`, `minus` and `times`.
* There is currently no support for divisions.
* There is barely any support for negative numbers.
* Only plus and minus expressions can be solved internally.
* Error reporting is less than ideal.
* While nesting of the big operators is possible (example: `\sum{i=0}^{2} \sum_{j=0}^{3} x_{i,j}`), it is not possible to let an operator determine the length of another (example of what does NOT work: `\sum_{i=0}^{2} \sum_{j=0}^{i} x_j`).

# Requirements
The header of your tex file must contain the following:  
* \newcommand{\T}[1]{\texttt{#1}} % Required for `if-then-else`.
* \newcommand{\markreplaceable}[1]{#1} % Necessary for marking formulas that aren't subscripted for replacement by big operands. Does nothing to alter the pdf output.

The following libraries must be installed for the code to work:  
* click 7.1.2
* parsimonious 0.8.1
* regex 2020.9.27

# List of operands
Table of all repeatable operands that require brackets:
Operand                   | tex equivalent  | example
------------------------- | --------------- | ------- 
plus                      | `+`             | `(5 + 3)`
minus                     | `-`             | `(3 - i - 5)`
times                     | `\cdot`         | `(8 \cdot 3)`
less than                 | `<`             | `(a < b < 7 < 9)`
less than or equal to     | `\leq`          | `(a \leq b \leq 7 \leq 9)`
greater than              | `>`             | `(5 > 3)`
greater than or equal to  | `\geq`          | `(5 \geq 3)`
equals/bi-implication     | `=`             | `(4 = 3)`
and                       | `\land`         | `(a \land b \land c)`
or                    	  | `\lor`          | `(a \lor b)`
implies                   | `\to`           | `(a \to b \to c \to d)`

Table of operands that cannot be repeated and do not require brackets:
Special operands          | tex equivalent                            | example
------------------------- | ----------------------------------------- | -------
not                       | `\lnot`                                   | `\lnot a`
big and                   | `\bigwedge`                               | `\bigwedge_{i=0}^{5} (a_i \land b_i)`
big and (alt)             | `\bigwedge`                               | `\bigwedge_{i,j:0\leq i<j<5} (a_i \lor b_i)`
big or                    | `\bigvee`                                 | `\bigvee_{var=0}^{5-3} (a_var > b_{var, var+1})`
big or (alt)              | `\bigvee`                                 | `\bigvee_{var:0\leq var<5-3} (a_var > b_{var, var+1}`
sum                       | `\sum`                                    | `\sum_{a=2}^{3} (\markreplaceable{a} - b_a)`
sum (alt)                 | `\sum`                                    | `\sum_{a,b,c,d:0<a<b<c<d\leq6} ((x_a + x_b) - (x_c + x_d))`
if-then-else              | `\T{if} expr \T{then} expr \T{else} expr` | `\T{if} a \T{then} 5 \T{else} 3`



