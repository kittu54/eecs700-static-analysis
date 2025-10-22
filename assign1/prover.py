from z3 import *

def wp(stmt, post):
    if stmt[0] == 'seq':
        for s in reversed(stmt[1:]):
            post = wp(s, post)
        return post
    elif stmt[0] == 'assume':
        cond = expr_to_z3(stmt[1])
        return Implies(cond, post)
    elif stmt[0] == 'assert':
        cond = expr_to_z3(stmt[1])
        return And(cond, post)
    elif stmt[0] == 'if':
        test = expr_to_z3(stmt[1])
        body = stmt[2]
        orelse = stmt[3]
        wp_body = wp(['seq'] + body, post)
        wp_orelse = wp(['seq'] + orelse, post)
        return And(Implies(test, wp_body), Implies(Not(test), wp_orelse))
    elif stmt[0] == 'skip':
        return post
    elif stmt[0] == 'assign':
        var = stmt[1]
        expr = expr_to_z3(stmt[2])
        return substitute(post, (Int(var), expr))

    elif stmt[0] == 'invariant':
        # invariants do not affect the weakest precondition
        return BoolVal(True)


    elif stmt[0] == 'while':
        cond = expr_to_z3(stmt[1])
        invariant = And(*list(map(expr_to_z3, stmt[3])))
        body = stmt[2]
        wp_body = wp(['seq'] + body, invariant)
        return And(invariant, Implies(And(invariant, cond), wp_body), Implies(And(invariant, Not(cond)), post))

    
    else:
        raise NotImplementedError(stmt)

def expr_to_z3(expr):
    if expr[0] == 'const':
        if isinstance(expr[1], bool):
            return BoolVal(expr[1])
        else:
            return IntVal(expr[1])
    elif expr[0] == 'var':
        return Int(expr[1])
    elif expr[0] == '<':
        return expr_to_z3(expr[1]) < expr_to_z3(expr[2])
    elif expr[0] == '<=':
        return expr_to_z3(expr[1]) <= expr_to_z3(expr[2])
    elif expr[0] == '>':
        return expr_to_z3(expr[1]) > expr_to_z3(expr[2])
    elif expr[0] == '>=':
        return expr_to_z3(expr[1]) >= expr_to_z3(expr[2])
    elif expr[0] == '==':
        return expr_to_z3(expr[1]) == expr_to_z3(expr[2])
    elif expr[0] == '!=':
        return expr_to_z3(expr[1]) != expr_to_z3(expr[2])
    elif expr[0] == '+':
        return expr_to_z3(expr[1]) + expr_to_z3(expr[2])
    elif expr[0] == '-':
        if len(expr) == 2:
            return -expr_to_z3(expr[1])
        else:
            return expr_to_z3(expr[1]) - expr_to_z3(expr[2])
    elif expr[0] == '*':
        return expr_to_z3(expr[1]) * expr_to_z3(expr[2])
    elif expr[0] == '/':
        return expr_to_z3(expr[1]) / expr_to_z3(expr[2])
    elif expr[0] == '==':
        return expr_to_z3(expr[1]) == expr_to_z3(expr[2])
    else:
        raise NotImplementedError(expr)



def prove(stmt):
    post = BoolVal(True)
    pre = wp(stmt, post)
    print(pre)
    s = Solver()
    s.add(Not(pre))
    if s.check() == unsat:
        print("The program is correct.")
    else:
        print("The program is incorrect.")
        print(s.model())

if __name__ == "__main__":
    from parser import py_ast, WhilePyVisitor
    import sys
    filename = sys.argv[1]
    tree = py_ast(filename)
    visitor = WhilePyVisitor()
    stmt = visitor.visit(tree)
    print("Program AST:", stmt)
    prove(stmt)
