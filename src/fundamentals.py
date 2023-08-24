from __future__ import annotations

#################################################################################

from typing import List, NamedTuple, Sequence, Tuple, Union
from abc import ABC
from dataclasses import dataclass

#################################################################################
#################################################################################
#                                   CONTENTS:
# - FUNDAMETALS:
#   - VARIABLES
#   - SIGNED VARIABLES
#   - BOUND VALUES
#   - LITERALS
#
# - FUNDAMETALS II:
#   - CONSTRAINT EXPRESSION ATOMS
#   - CONSTRAINT EXPRESSIONS
#
# - FUNDAMETALS III:
#   - CONSTRAINT ELEMENTARY EXPRESSIONS
#   - REIFIED CONSTRAINTS
#
# - HELPER CLASS: TIGHT DISJUNCTIONS
#################################################################################
#################################################################################

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

ZERO_VAR = Var(0)
"""
A special Zero variable whose domain will always be equal to the {0} singleton.
"""

#################################################################################
# SIGNED VARIABLES
#################################################################################

class SignedVar(NamedTuple):
    """
    Represents a "signed variable", which is a positive or negative "view" of a variable.
    
    Simply put, a variable v can have two signed variables (+v and -v).
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

class BoundVal(int):
    """
    Represents signed variables' (upper) bound values.

    This allows to represent both upper and lower bound values of variables in an identical way.
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_stronger_than(self,
        other_bound_value: BoundVal,
    ) -> bool:
        """
        Args:
            other_bound_value (BoundVal): Other bound value to compare to.
        
        Returns:
            bool: Whether the bound value is stronger (i.e. equal or less) than `other_bound_value`.
        """
        return self <= other_bound_value

#################################################################################
# LITERALS
#################################################################################

class Lit(NamedTuple):
    """
    Represents a literal (aka "bound-literal"), which is an expression on the
    lower or upper bound of a variable.
        
    To deal with the cases of lower and upper bounds in identical ways, a literal
    actually represents an expression on the upper bound of a signed variable.
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    signed_var: SignedVar
    """
    The signed variable of the literal.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    bound_value: BoundVal
    """
    The (upper) bound value of the literal.
    """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def leq(cls,
        var: Var,
        value: int     
    ) -> Lit:
        """
        s: The [`var` <= `value`] literal (i.e. [+`var` <= +`value`]).
        """
        return Lit(SignedVar(var, True), BoundVal(value))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def geq(cls,
        var: Var,
        value: int     
    ) -> Lit:
        """
        Returns:
            Lit: The [`var` >= `value`] literal (i.e. [-`var` <= -`value`]).
        """
        return Lit(SignedVar(var, False), BoundVal(-value))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
    def negation(self) -> Lit:
        """
        Returns:
            Lit: The negation of the literal.
        """
        return Lit(self.signed_var.opposite_signed_var(), BoundVal(-self.bound_value-1))
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    
    def entails(self,
        other_literal: Lit,
    ) -> bool:
        """
        Returns:
            bool: Whether this literal entails `other_literal`.
        (i.e. it is on the same signed variable and has a stronger bound value).
        """
        return (self.signed_var == other_literal.signed_var
            and self.bound_value.is_stronger_than(other_literal.bound_value))

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

TRUE_LIT = Lit.leq(ZERO_VAR, 0)
"""
A special True (or tautology) literal.

Corresponds to the [ZERO_VAR <= 0] literal.

Relies on the fact that the special Zero variable is always equal to 0,
"""

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

FALSE_LIT = TRUE_LIT.negation()
"""
A special False (or contradiction) literal.

Is the negation of the "True" literal, which corresponds to
the [ZERO_VAR >= 1] literal (i.e. [-ZERO_VAR <= -1]).
"""

#################################################################################
# CONSTRAINT EXPRESSION ATOMS
#################################################################################

class ConstraintExpressionAtoms(ABC):
    """
    TODO
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Bool(NamedTuple):
        var: Var

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Int(NamedTuple):
        var: Var
        offset: int

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Sym(NamedTuple):
        var: Var
        sym_type: None #FIXME

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    AnyAtom = Union[
        Bool,
        Int,
#        Ratio,
        Sym,
    ]

#################################################################################
# CONSTRAINT EXPRESSIONS
#################################################################################

class ConstraintExpression(ABC):
    """
    TODO
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Leq(NamedTuple):
        left_atom: ConstraintExpressionAtoms.Int
        right_atom: ConstraintExpressionAtoms.Int

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Lt(NamedTuple):
        left_atom: ConstraintExpressionAtoms.Int
        right_atom: ConstraintExpressionAtoms.Int

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Geq(NamedTuple):
        left_atom: ConstraintExpressionAtoms.Int
        right_atom: ConstraintExpressionAtoms.Int

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Gt(NamedTuple):
        left_atom: ConstraintExpressionAtoms.Int
        right_atom: ConstraintExpressionAtoms.Int

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Eq(NamedTuple):
        atom1: ConstraintExpressionAtoms.AnyAtom
        atom2: ConstraintExpressionAtoms.AnyAtom

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Neq(NamedTuple):
        atom1: ConstraintExpressionAtoms.AnyAtom
        atom2: ConstraintExpressionAtoms.AnyAtom

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Or(NamedTuple):
        literals: Tuple[Lit,...]

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class And(NamedTuple):
        literals: Tuple[Lit,...]

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Imply(NamedTuple):
        from_literal: Lit
        to_literal: Lit

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    AnyExpr = Union[
        Leq,
        Lt,
        Geq,
        Gt,
        Eq,
        Neq,
        Or,
        And,
        Imply,
    ]

#################################################################################
# CONSTRAINT ELEMENTARY EXPRESSIONS
#################################################################################

class ConstraintElementaryExpression(ABC):
    """
    TODO
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class LitExpr(NamedTuple):
        literal: Lit

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def negation(self) -> ConstraintElementaryExpression.LitExpr:
            return ConstraintElementaryExpression.LitExpr(self.literal.negation())

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Or(NamedTuple):
        literals: Tuple[Lit,...]

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def negation(self) -> ConstraintElementaryExpression.And:
            return ConstraintElementaryExpression.And(tuple(lit.negation() for lit in self.literals))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class And(NamedTuple):
        literals: Tuple[Lit,...]

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def negation(self) -> ConstraintElementaryExpression.Or:
#            return ConstraintElementaryExpression.Or(TightDisjunction(tuple(lit.negation() for lit in self.literals)).literals)
            return ConstraintElementaryExpression.Or(tuple(lit.negation() for lit in self.literals))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class MaxDiffCnt(NamedTuple):
        from_var: Var
        to_var: Var
        max_diff: int

        # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

        def negation(self) -> ConstraintElementaryExpression.MaxDiffCnt:
            return ConstraintElementaryExpression.MaxDiffCnt(self.to_var, self.from_var, -self.max_diff-1)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    #def MaxDiffCtg(NamedTuple):
    #    from_var: Var
    #    to_var: Var
    #    max_diff: int

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    #def Linear(NamedTuple):
    #    ...

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    AnyExpr = Union[
        LitExpr,
        Or,
        And,
        MaxDiffCnt,
    ]

#################################################################################
# REIFIED CONSTRAINTS
#################################################################################

class ReifiedConstraint(NamedTuple):
    """
    TODO
    """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    constraint_elementary_expression: ConstraintElementaryExpression.AnyExpr
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    reification_literal: Lit

#################################################################################
# TIGHT DISJUNCTIONS
#################################################################################

@dataclass(frozen=True, init=False)
class TightDisjunction():
    """
    Helper class that transforms (or "tightens") a disjunction of literals into
    so-called "tight form", meaning the literals are sorted (in lexicographic order)
    and, in case there were initially multiple literals on the same signed variable,
    only one (the weakest) is kept.

    After the tightening, the literals in tightened may be used freely anywhere.
    
    Note that nowhere in the code is it "fundamentally required" for a disjunction
    of literals to be in tight form. However, it is desirable, for example to
    reduce the size of clauses or explanations, which is why tightening is used
    at some specific moments.
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    literals: Tuple[Lit,...]
    """
    The "tightened" literals of the disjunction. They are sorted in lexicographic
    order and there is only one literal per signed variable.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
    _already_tight: bool
    """
    Whether the literals given initially were indicated as already in tight form.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def __init__(self,
        literals: Sequence[Lit],
        _already_tight: bool=False,
    ):
        object.__setattr__(self, '_already_tight', _already_tight)

        # If the literals are indicated as already in tight form,
        if self._already_tight:
            object.__setattr__(self, 'literals', tuple(literals))

        # Otherwise, tighten them.
        else:
            lits: List[Lit] = sorted(literals)

            n = len(lits)
            i = 0
            j = 0
            while i < n-1-j:
                # Because the literals are now lexicographically sorted,
                # we know that if two literals are on the same signed variable,
                # the weaker one is necessarily the next one.
                if lits[i].entails(lits[i+1]):
                    lits.pop(i)
                    j += 1
                else:
                    i += 1

            object.__setattr__(self, 'literals', tuple(lits))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_tautological(self) -> bool:
        """
        Returns:
            bool: Whether the disjunction is tautological
        (i.e. is always true, because of two literals [v<=x] and [v>=y] with y<=x).
        """
        
        n = len(self.literals)
        i = 0
        while i < n-1:
            if self.literals[i].signed_var.opposite_signed_var() == self.literals[i+1].signed_var:
                if self.literals[i].bound_value - self.literals[i+1].bound_value <= 0:
                    return True
            i += 1
        return False        

#################################################################################
