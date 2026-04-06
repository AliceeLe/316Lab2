"""
Information flow analysis for the C0 subset.

Students must implement:
  check_secure(prog) - returns True if secure, False otherwise
"""

import c0


def join(l1: str, l2: str) -> str:
    """Join (lub) of two security labels. H dominates L."""
    return "H" if "H" in (l1, l2) else "L"


def leq(l1: str, l2: str) -> bool:
    """True if l1 ⊑ l2 in the lattice L ⊑ H."""
    return l1 == "L" or l2 == "H"


def check_secure(prog: c0.Program) -> bool:
    """Termination-sensitive information flow type checker.

    Returns True if the program is secure, False otherwise.
    """
    # Security environment stack: each frame maps variable names -> "H" or "L"
    sec_stack = [{"input": "L", "secret": "H"}]

    def lookup(name: str) -> str:
        for env in reversed(sec_stack):
            if name in env:
                return env[name]
        return "L"  # fallback (parser ensures all vars declared)

    def label_exp(exp: c0.Exp) -> str:
        """Compute the security label of an expression."""
        if isinstance(exp, (c0.IntConst, c0.BoolConst)):
            return "L"
        if isinstance(exp, c0.Var):
            return lookup(exp.name)
        if isinstance(exp, c0.BinOp):
            return join(label_exp(exp.left), label_exp(exp.right))
        if isinstance(exp, c0.UnOp):
            return label_exp(exp.arg)
        if isinstance(exp, c0.Length):
            # \length(A) has the label of the array A
            return label_exp(exp.arg)
        if isinstance(exp, c0.ArrayAccess):
            # A[i]: label is join of array label and index label
            return join(label_exp(exp.arr), label_exp(exp.index))
        return "L"  # fallback

    def check_stmt(stmt: c0.Stmt, pc: str) -> bool:
        """
        Check a statement under program-counter label pc.
        Returns True if secure, False if insecure.
        Mutates sec_stack for declarations.
        """
        if isinstance(stmt, c0.Decl):
            var_label = stmt.label if stmt.label is not None else "L"
            # pc must flow into variable label (implicit flow)
            if not leq(pc, var_label):
                return False
            # Initializer label must flow into variable label
            if stmt.init is not None:
                if not leq(label_exp(stmt.init), var_label):
                    return False
            sec_stack[-1][stmt.name] = var_label
            return True

        if isinstance(stmt, c0.AllocArray):
            # dest was declared just before this (Decl + AllocArray pair)
            arr_label = lookup(stmt.dest)
            # pc must flow into array label
            if not leq(pc, arr_label):
                return False
            # count expression label must flow into array label
            if not leq(label_exp(stmt.count), arr_label):
                return False
            return True

        if isinstance(stmt, c0.Assign):
            dest_label = lookup(stmt.dest)
            if not leq(label_exp(stmt.source), dest_label):
                return False
            if not leq(pc, dest_label):
                return False
            return True

        if isinstance(stmt, c0.ArrWrite):
            # arr must be a Var (enforced by parser)
            if not isinstance(stmt.arr, c0.Var):
                return False
            arr_label = lookup(stmt.arr.name)
            # index label, value label, and pc must all flow into array label
            if not leq(label_exp(stmt.index), arr_label):
                return False
            if not leq(label_exp(stmt.val), arr_label):
                return False
            if not leq(pc, arr_label):
                return False
            return True

        if isinstance(stmt, c0.Block):
            sec_stack.append({})
            for s in stmt.stmts:
                if not check_stmt(s, pc):
                    sec_stack.pop()
                    return False
            sec_stack.pop()
            return True

        if isinstance(stmt, c0.If):
            cond_label = label_exp(stmt.cond)
            new_pc = join(pc, cond_label)
            if not check_stmt(stmt.true_branch, new_pc):
                return False
            if stmt.false_branch is not None:
                if not check_stmt(stmt.false_branch, new_pc):
                    return False
            return True

        if isinstance(stmt, c0.While):
            cond_label = label_exp(stmt.cond)
            new_pc = join(pc, cond_label)
            # Termination-sensitive: loop condition (and context) must be L.
            # A high-label condition or a high pc creates a termination channel.
            if new_pc != "L":
                return False
            return check_stmt(stmt.body, new_pc)

        if isinstance(stmt, c0.Assert):
            cond_label = label_exp(stmt.cond)
            # Termination-sensitive: assert aborts if cond is false.
            # Abort in a high context leaks information through termination.
            if join(pc, cond_label) != "L":
                return False
            return True

        if isinstance(stmt, c0.Error):
            # error() always aborts.
            # Termination-sensitive: abort in high context leaks info.
            if pc != "L":
                return False
            return True

        if isinstance(stmt, c0.Return):
            # Return value must be low (it is a low observation).
            if stmt.val is not None:
                if not leq(label_exp(stmt.val), "L"):
                    return False
            # pc must be L (implicit flow: returning vs not returning leaks H).
            if not leq(pc, "L"):
                return False
            return True

        # Unknown statement form — assume secure (shouldn't happen after parsing)
        return True

    try:
        for stmt in prog.stmts:
            if not check_stmt(stmt, "L"):
                return False
        return True
    except Exception:
        return False
