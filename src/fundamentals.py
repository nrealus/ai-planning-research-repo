from __future__ import annotations

#################################################################################

from dataclasses import dataclass

from typing import Tuple, NamedTuple, Union, Dict, Iterable
from abc import ABC

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
#   - CONSTRAINT FORMULAS AND REIFIED CONSTRAINTS
#################################################################################
#################################################################################

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

        return (self.signed_var == other_literal.signed_var
            and self.bound_value.is_stronger_than(other_literal.bound_value))

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
# CONSTRAINT FORMULAS AND REIFIED CONSTRAINTS
#################################################################################

class ConstrFormula(ABC):
    """
    A container or "namespace" containing types representing constraint formulas
    (like a single literal, a conjunction of literals, a disjunction of literals,
    or a maximum difference between two variables).

    A constraint's formula is obtained by interpreting/decomposing/converting a
    constraint's expression. The symbols in the expression are
    interpreted/decomposed/converted into this "formula format".
    For example, an equality is converted to a conjunction of two literals (which
    is itself converted to a disjunction of two literals).

    In a nutshell, a constraint's expression defines a constraint at a high level,
    and a constraint's formula defines a constraint on a low level.
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class SingleLit(NamedTuple):
        literal: Literal

        def negation(self) -> ConstrFormula.SingleLit:
            return ConstrFormula.SingleLit(self.literal.negation())

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Or(NamedTuple):
        literals: Tuple[Literal,...]

        def negation(self) -> ConstrFormula.And:
            return ConstrFormula.And(tuple(lit.negation() for lit in self.literals))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class And(NamedTuple):
        literals: Tuple[Literal,...]

        def negation(self) -> ConstrFormula.Or:
            return ConstrFormula.Or(tuple(lit.negation() for lit in self.literals))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class MaxDiffCnt(NamedTuple):
        from_var: Var
        to_var: Var
        max_diff: int

        def negation(self) -> ConstrFormula.MaxDiffCnt:
            return ConstrFormula.MaxDiffCnt(
                self.to_var,
                self.from_var,
                -self.max_diff-1,   # NOTE: -1 just sitting here
            )

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    #def MaxDiffCtg(NamedTuple):
    #    from_var: Var
    #    to_var: Var
    #    max_diff: int

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    #def Linear(NamedTuple):
    #    ...

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    Any = Union[
        SingleLit,
        Or,
        And,
        MaxDiffCnt,
    ]

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

class ReifiedConstraint(NamedTuple):
    constr_formula: ConstrFormula.Any
    reification_literal: Literal

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

class ConstrExprGrammar(ABC):

#    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#
#    class Or(NamedTuple):
#        ...
#
#    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#
#    class And(NamedTuple):
#        ...
#
#    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#
#    class Eq(NamedTuple):
#        ...
#
#    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#
#    class Leq(NamedTuple):
#        ...
#
#    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#
#       ...
#
#    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    Any = Union[
        object, object
#        Or,
#        And,
#        Eq,
#        Leq,
#       ....
    ]

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

ConstrExpr = Dict[ConstrExprGrammar.Any, Iterable['ConstrExpr']]
