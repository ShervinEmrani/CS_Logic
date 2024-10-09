from sympy import sympify, sift, ordered, filldedent
from sympy.logic import simplify_logic
from sympy.logic.boolalg import to_cnf, is_cnf, POSform, _sop_form, _get_truthtable, _find_predicates, BooleanFunction, \
    is_literal, is_dnf, Not, distribute_and_over_or, eliminate_implications


def simpify_logic(expr, form=None, deep=True, force=False, dontcare=None):
    if form not in (None, 'cnf', 'dnf'):
        raise ValueError("form can be cnf or dnf only")
    expr = sympify(expr)
    # check for quick exit if form is given: right form and all args are
    # literal and do not involve Not
    if form:
        form_ok = False
        if form == 'cnf':
            form_ok = is_cnf(expr)
        elif form == 'dnf':
            form_ok = is_dnf(expr)

        if form_ok and all(is_literal(a)
                for a in expr.args):
            return expr
    from sympy.core.relational import Relational
    if deep:
        variables = expr.atoms(Relational)
        from sympy.simplify.simplify import simplify
        s = tuple(map(simplify, variables))
        expr = expr.xreplace(dict(zip(variables, s)))
    if not isinstance(expr, BooleanFunction):
        return expr
    # Replace Relationals with Dummys to possibly
    # reduce the number of variables
    repl = {}
    undo = {}
    from sympy.core.symbol import Dummy
    variables = expr.atoms(Relational)
    if dontcare is not None:
        dontcare = sympify(dontcare)
        variables.update(dontcare.atoms(Relational))
    while variables:
        var = variables.pop()
        if var.is_Relational:
            d = Dummy()
            undo[d] = var
            repl[var] = d
            nvar = var.negated
            if nvar in variables:
                repl[nvar] = Not(d)
                variables.remove(nvar)

    expr = expr.xreplace(repl)

    if dontcare is not None:
        dontcare = dontcare.xreplace(repl)

    # Get new variables after replacing
    variables = _find_predicates(expr)
    if not force and len(variables) > 8:
        return expr.xreplace(undo)
    if dontcare is not None:
        # Add variables from dontcare
        dcvariables = _find_predicates(dontcare)
        variables.update(dcvariables)
        # if too many restore to variables only
        if not force and len(variables) > 8:
            variables = _find_predicates(expr)
            dontcare = None
    # group into constants and variable values
    c, v = sift(ordered(variables), lambda x: x in (True, False), binary=True)
    variables = c + v
    # standardize constants to be 1 or 0 in keeping with truthtable
    c = [1 if i == True else 0 for i in c]
    truthtable = _get_truthtable(v, expr, c)
    if dontcare is not None:
        dctruthtable = _get_truthtable(v, dontcare, c)
        truthtable = [t for t in truthtable if t not in dctruthtable]
    else:
        dctruthtable = []
    big = len(truthtable) >= (2 ** (len(variables) - 1))
    if form == 'dnf' or form is None and big:
        return _sop_form(variables, truthtable, dctruthtable).xreplace(undo)
    return POSform(variables, truthtable, dctruthtable).xreplace(undo)


def to_cnf_(expr, simplify=False, force=False):

    expr = sympify(expr)
    if not isinstance(expr, BooleanFunction):
        return expr

    if simplify:
        if not force and len(_find_predicates(expr)) > 8:
            raise ValueError(filldedent('''
            To simplify a logical expression with more
            than 8 variables may take a long time and requires
            the use of `force=True`.'''))
        return simplify_logic(expr, 'cnf', True, force=force)

    # Don't convert unless we have to
    if is_cnf(expr):
        return expr

    expr = eliminate_implications(expr)
    res = distribute_and_over_or(expr)

    return res


def new_expression(expression):
    replacements = {
        r'\wedge': '&',         
        r'\vee': '|',          
        r'\rightarrow': '>>',      
        r'\neg': '~'              
    }
    for old, new in replacements.items():
        expression = expression.replace(old, new)
    return expression


def show_latex_expression(expression):
    replacements = {
        '&': r'\wedge',        
        '|': r'\vee',          
        '>>': r'\rightarrow',     
        '~': r'\neg'             
    }
    for new, old in replacements.items():
        expression = expression.replace(new, old)
    return expression


def is_well_formed(exp):
    try:
        simplify_logic(exp)
        return True
    except:
        return False


# Get input from the user in LaTeX format for a propositional expression
expression = new_expression(input("Input formula: "))

# Check if the expression is well-formed
if is_well_formed(expression):
    print('\nexpression is well formed\n')
else:
    print('expression is not well formed\n')
    quit()
# Convert the final expression to Conjunctive Normal Form (CNF) and print the result
CNF_form = str(to_cnf(expression))
print(CNF_form)
output = show_latex_expression(CNF_form)
print(output)
