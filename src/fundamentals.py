"""
This module defines the basic, fundamental building blocks used in the project.
"""

from __future__ import annotations

#################################################################################

from typing import List, NamedTuple, Sequence, Tuple

#################################################################################
# VARIABLES
#################################################################################

class Var(NamedTuple):
    """Represents a variable."""
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    var_id: int

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

ZERO_VAR = Var(0)
"""
A special instance of `Var` whose domain will be assumed to be the single value 0.
"""

#################################################################################
# SIGNED VARIABLES
#################################################################################

class SignedVar(NamedTuple):
    """
    Represents so-called signed variables. A `SignedVar` 
    is a positive or negative view on a `Var`.
    
    The positive (resp. negative) signed variable for variable `var` is
    defined as `SignedVar(var, True)` (resp. `SignedVar(var, False)`).
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    var: Var
    """The `SignedVar`'s variable."""

    plus_sign: bool
    """The `SignedVar`'s sign (True: +, False: -)."""

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @property
    def opposite(self) -> SignedVar:
        """The `SignedVar`'s opposite (same variable, opposite sign)."""
        return SignedVar(self.var, not self.plus_sign)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def plus(cls,
        var: Var,
    ) -> SignedVar:
        """Syntactic sugar for `SignedVar(var, True)`."""
        return SignedVar(var, True)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def minus(cls,
        var: Var,
    ) -> SignedVar:
        """Syntactic sugar for `SignedVar(var, False)`."""
        return SignedVar(var, False)

#################################################################################
# BOUND VALUES
#################################################################################

class BoundVal(int):
    """
    Represents the value of an upper bound on a `SignedVar`. As such,
    it also represents the value of a lower or upper bound on a `Var`.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def __neg__(self) -> BoundVal:
        return BoundVal(-int(self))

    def __add__(self,
        other_bound_val: BoundVal
    ) -> BoundVal:
        return BoundVal(int(self)+other_bound_val)

    def __sub__(self,
        other_bound_val: BoundVal
    ) -> BoundVal:
        return BoundVal(int(self)-other_bound_val)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_stronger_than(self,
        other_bound_value: BoundVal,
    ) -> bool:
        """
        Args:
            other_bound_value: Other bound value to compare to.
        
        Returns:
            Whether the bound value is stronger (i.e. equal or less)    \
                than `other_bound_value`.
        """
        return self <= other_bound_value

#################################################################################
# LITERALS
#################################################################################

class Lit(NamedTuple):
    """
    Represents an upper bound on a `SignedVar`. As such, it
    actually represents an upper bound or a lower bound on a `Var`.
        
    For example, `Lit(SignedVar(var, True), BoundVal(5))` (which we
    sometimes write `[var<=5]` as a shortcut in text) represents the
    expression "the value of variable `var` is less than or equal to 5".
    Similarly `Lit(SignedVar(var, False), BoundVal(-5))` represents the
    expression "the value of variable `var` is greater than or equal to 5".
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    signed_var: SignedVar
    """The `Lit`'s signed variable"""

    bound_value: BoundVal
    """The value of the `Lit`'s (upper) bound."""
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @property
    def negated(self) -> Lit:
        """The `Lit`'s negation."""
        return Lit(self.signed_var.opposite, -self.bound_value-BoundVal(1))
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def leq(cls,
        var: Var,
        value: int     
    ) -> Lit:
        """
        Syntactic sugar for `Lit(SignedVar.plus(var), BoundVal(value))`, which
        represents the `[var <= value]` literal.
        """
        return Lit(SignedVar.plus(var), BoundVal(value))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def geq(cls,
        var: Var,
        value: int     
    ) -> Lit:
        """
        Syntactic sugar for `Lit(SignedVar.minus(var), BoundVal(-value))`, which
        represents the `[var >= value]` literal.
        """
        return Lit(SignedVar.minus(var), BoundVal(-value))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
    def entails(self,
        other_literal: Lit,
    ) -> bool:
        """
        Args:
            other_literal: Another literal.

        Returns:
            Whether this literal entails `other_literal` (i.e. it is on the \
                same signed variable and has a stronger bound value).
        """
        return (self.signed_var == other_literal.signed_var
                and self.bound_value.is_stronger_than(other_literal.bound_value))

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

TRUE_LIT = Lit.leq(ZERO_VAR, 0)
"""
A special "true" (or tautology) literal.

Corresponds to the `[ZERO_VAR <= 0]` literal.

Relies on the fact that the `ZERO_VAR`'s value is always 0,
"""

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

FALSE_LIT = TRUE_LIT.negated
"""
A special "false" (or contradiction) literal.

Is the negation of the true literal, which corresponds to the `[ZERO_VAR >= 1]` literal.
"""

#################################################################################
# TIGHTENING OF (DISJUNCTIONS OF) LITERALS
#################################################################################

def tighten_literals(
    literals: Sequence[Lit]
) -> Tuple[Lit,...]:
    """
    "Tightens" a (disjunctive) set of literals. This means sorting them
    in lexicographic order (as tuples) and, in case there are multiple
    of them on the same `SignedVar`, only keeping the weakest one.
     
    Args:
        literals: A set of literals
    
    Returns:
        A "tightened" or "tight" set of literals.
    """

    lits: List[Lit] = sorted(literals)

    n = len(lits)
    i = 0
    j = 0
    while i < n-1-j:
        # Because the literals are now lexicographically sorted,
        # we know that if two literals are on the same signed
        # variable, the weaker one is necessarily the next one.
        if lits[i].entails(lits[i+1]):
            lits.pop(i)
            j += 1
        else:
            i += 1

    return tuple(lits)

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

def are_tightened_literals_tautological(
    literals: Tuple[Lit,...]
) -> bool:
    """
    Args:
        literals: A set of literals, assumed to be tight.

    Returns:
        Whether the disjunction formed by then given literals is \
            tautological (i.e. is always true, because of two    \
            literals `[var<=a]` and `[var>=b]` with `a<=b`).

    Raises:
        ValueError: If the given set of literals is empty.
        ValueError: If the given set of literals is not tight.
    """

    n = len(literals)

    if n == 0:
        raise ValueError(("Attempt to check whether an empty set of literals is tautological. "
                          "Technically, an empty set of literals is indeed tautological. However, "
                          "at no point do we want a set of literals passed to this method "
                          "to be empty, so we raise an error to further enforce that."))
    i = 0
    while i < n-1:

        if not (literals[i] < literals[i+1]
                and literals[i].signed_var != literals[i+1].signed_var
        ):
            raise ValueError(("The set of literals given to ",
                             "`are_tightened_literals_tautological` is not tightened."))

        if literals[i].signed_var.opposite == literals[i+1].signed_var:
            if literals[i].bound_value - literals[i+1].bound_value <= 0:
                return True
        i += 1

    return False
