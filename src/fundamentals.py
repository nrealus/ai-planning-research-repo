from __future__ import annotations

#################################################################################

from dataclasses import dataclass

from typing import Tuple, NamedTuple, List, Optional

#################################################################################
#################################################################################
#                                 CONTENTS:
# - BASIC UTILITIES
# - FUNDAMETALS I:
#   - VARIABLES
#   - SIGNED VARIABLES
#   - BOUND VALUES
#   - LITERALS
# - FUNDAMETALS II:
#   - CLAUSES
#################################################################################
#################################################################################

AssertUnreachable = AssertionError("UNREACHABLE CODE")
"""
Used to mark unreachable locations in code, both for readability
and for correct type checking.
"""

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

# DEBUG: bool = True
# 
# def debug_assert(cond: bool, msg: Optional[str]=None):
# 
#     if not DEBUG:
#         return
# 
#     if msg is None:
#         assert cond
#     else:
#         assert cond, msg

#################################################################################
# VARIABLES
#################################################################################

class Var(NamedTuple):
    """
    Represents a variable.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    id: int

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

ZeroVar = Var(0)
"""
A special Zero variable whose domain will always be a singleton with the value 0.
"""

#################################################################################
# SIGNED VARIABLES
#################################################################################

class SignedVar(NamedTuple):
    """
    Represents a "signed variable", which is a positive or negative "view" on a variable.
    
    In other words, a variable v can have two signed variables, corresponding to +v and -v.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    var: Var
    """
    The variable of this signed variable.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    plus_sign: bool
    """
    The sign of the signed variable.

    +: True, -: False
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def opposite_signed_var(self) -> SignedVar:
        """
        Returns:
            SignedVar: The opposite signed variable.
        """

        return SignedVar(self.var, not self.plus_sign)

#################################################################################
# BOUND VALUES
#################################################################################

class BoundValue(int):
    """
    Represents signed variables' (upper) bound values.

    This allows to represent both upper and lower bound values of variables in an identical way.
    
    (see `Literal`)
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_stronger_than(self,
        other_bound_value: BoundValue,
    ):
        """
        Args:
            other_bound_value (BoundValue): Other bound value to compare to.
        
        Returns:
            bool: Whether the bound value is stronger (i.e. equal or less) than `other_bound_value`.
        """

        return self <= other_bound_value

#################################################################################
# LITERALS (A.K.A "BOUND LITERALS")
#################################################################################

class Literal(NamedTuple):
    """
    Represents a literal, which is an expression on the lower or upper bound of a variable.
    
    They can also be called "bound literals".
    
    To deal with the cases of lower and upper bounds in identical ways, a literal
    actually represents an expression on the upper bound of a signed variable.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    signed_var: SignedVar
    """
    The signed variable of the literal.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    bound_value: BoundValue
    """
    The (upper) bound value of the literal.
    """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
    def negation(self) -> Literal:
        """
        Returns:
            Literal: The negation of the literal.
        """

        return Literal(
            self.signed_var.opposite_signed_var(),
            BoundValue(-self.bound_value-1))
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
    def entails(self,
        other_literal: Literal,
    ) -> bool:
        """
        Returns:
            bool: Whether this literal entails `other_literal`.
        (i.e. it is on the same signed variable and has a stronger bound value).
        """

        assert self.signed_var == other_literal.signed_var

        return self.bound_value.is_stronger_than(other_literal.bound_value)

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

TrueLiteral = Literal(SignedVar(ZeroVar, True), BoundValue(0))
"""
A special True (or tautology) literal.

Corresponds to the [+ZeroVar <= 0] literal.

Relies on the fact that the special Zero variable is always equal to 0,
"""

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

FalseLiteral = TrueLiteral.negation()
"""
A special False (or contradiction) literal.

Is the negation of the "True" literal, which corresponds to the [-ZeroVar <= -1] literal.
"""

#################################################################################
# CLAUSES
#################################################################################

# A clause is a disjunction of literals.
# TODO: more documentation.
@dataclass
class Clause():
    """
    Represents a clause registered in a clause database (i.e. an already known
    or learned clause) for disjunctive/SAT reasoning.
    TODO
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    literals: Tuple[Literal,...]
    """
    TODO
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    scope: Literal
    """
    A literal that describes whether the clause is "active" or not.

    As such, the full clause is actually: (not scope) v l_1 v ... v l_n

    Note that a clause that is known to be violated but also inactive is not
    considered to be a conflict.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    learned: bool
    """
    Whether the clause is learned or not.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    watch1_index: int
    """
    Index of the first watched literal.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    watch2_index: int
    """
    Index of the second watched literal.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    unwatched_indices: List[int]
    """
    TODO
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
    def __init__(self,
        literals: Tuple[Literal,...],
        scope: Literal,
        learned: bool
    ):
        
        self.literals = literals

        len_literals = len(literals)
        assert len_literals > 0, "Empty clauses are not allowed."

        self.scope = scope
        self.learned = learned
        
        self.watch1_index = 0
        self.watch2_index = 1 if len_literals > 1 else 0
        self.unwatched_indices = list(range(2, len_literals)) if len_literals > 2 else []

#################################################################################