"""
Information flow analysis for the C0 subset.

Students must implement:
  check_secure(prog) - returns True if secure, False otherwise
"""

import c0


def join(l1: str, l2: str) -> str:
    return "H" if "H" in (l1, l2) else "L"


def leq(l1: str, l2: str) -> bool:
    return l1 == "L" or l2 == "H"


def mapVariable(name: str, stack) -> str:
    for env in reversed(stack):
        if name in env:
            return env[name]
    return "L"  # fallback


def label(exp: c0.Exp, stack) -> str:
    if isinstance(exp, (c0.IntConst, c0.BoolConst)):
        return "L"
    elif isinstance(exp, c0.Var):
        return mapVariable(exp.name, stack)
    elif isinstance(exp, c0.BinOp):
        return join(label(exp.left, stack), label(exp.right, stack))
    elif isinstance(exp, c0.UnOp) or isinstance(exp, c0.Length):
        return label(exp.arg, stack)
    elif isinstance(exp, c0.ArrayAccess):
        return join(label(exp.arr, stack), label(exp.index, stack))
    else:
        return "L"  # fallback


def check_secure(prog: c0.Program) -> bool:
    sec_stack = [{"input": "L", "secret": "H"}]

    def check_stmt(stmt: c0.Stmt, pc: str) -> bool:
        if isinstance(stmt, c0.Decl):
            var_label = stmt.label or "L"
            if not leq(pc, var_label):
                return False
            if stmt.init is not None:
                if not leq(label(stmt.init, sec_stack), var_label):
                    return False
            sec_stack[-1][stmt.name] = var_label
            return True

        elif isinstance(stmt, c0.AllocArray):
            arr_label = mapVariable(stmt.dest, sec_stack)  
            return leq(pc, arr_label) and leq(label(stmt.count, sec_stack), arr_label)

        elif isinstance(stmt, c0.Assign):
            dest_label = mapVariable(stmt.dest, sec_stack)  
            return leq(label(stmt.source, sec_stack), dest_label) and leq(pc, dest_label)

        elif isinstance(stmt, c0.ArrWrite):
            if not isinstance(stmt.arr, c0.Var):
                return False
            arr_label = mapVariable(stmt.arr.name, sec_stack)  
            return (
                leq(label(stmt.index, sec_stack), arr_label)
                and leq(label(stmt.val, sec_stack), arr_label)
                and leq(pc, arr_label)
            )

        elif isinstance(stmt, c0.Block):
            sec_stack.append({})
            for s in stmt.stmts:
                if not check_stmt(s, pc):
                    sec_stack.pop()
                    return False
            sec_stack.pop()
            return True

        elif isinstance(stmt, c0.If):
            new_pc = join(pc, label(stmt.cond, sec_stack))
            if not check_stmt(stmt.true_branch, new_pc):
                return False
            if stmt.false_branch is not None and not check_stmt(stmt.false_branch, new_pc):
                return False
            return True

        elif isinstance(stmt, c0.While):
            new_pc = join(pc, label(stmt.cond, sec_stack))
            return new_pc == "L" and check_stmt(stmt.body, new_pc)

        elif isinstance(stmt, c0.Assert):
            return join(pc, label(stmt.cond, sec_stack)) == "L"

        elif isinstance(stmt, c0.Error):
            return pc == "L"

        elif isinstance(stmt, c0.Return):
            return (stmt.val is None or leq(label(stmt.val, sec_stack), "L")) and leq(pc, "L")

        else:
            return True

    try:
        for stmt in prog.stmts:
            if not check_stmt(stmt, "L"):
                return False
        return True
    except Exception:
        return False