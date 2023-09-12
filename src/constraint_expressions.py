"""
This module defines both "high-level" and "low-level" constraint expressions.

"High-level" (or "natural") constraint expressions (`ConstrExpr`) are specified
by the user and fed to the solver. "Low-level" (or "elementary") constraint
expressions (`ElemConstrExpr`) are used internally by the solver, and are obtained
by the decomposing "high-level" constraint expressions.
"""

from __future__ import annotations

#################################################################################

from enum import Enum, auto
from typing import NamedTuple, Sequence, Tuple, Union

from .fundamentals import (FALSE_LIT, TRUE_LIT, ZERO_VAR, Lit, Var,
                          are_tightened_literals_tautological,
                          tighten_literals)

#################################################################################
# ("NATURAL") CONSTRAINT EXPRESSIONS
#################################################################################

class ConstrExpr(NamedTuple):
    """
    Represents a "high-level" or "natural" constraint, specified by the user.

    Warning:
        No errors will be raised if an incorrect / inconsistent / incompatible\
            instantiation is made (i.e. constraint type and terms are inconsistent).\
            However, errors may be raised during further processing, if the\
            expression cannot be interpreted.
    """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Kind(Enum):
        LEQ = auto()
        LT = auto()
        GEQ = auto()
        GT = auto()
        EQ = auto()
        NEQ = auto()
        OR = auto()
        AND = auto()
        IMPLY = auto()
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    kind: Kind
    """Represents the type or kind of constraint."""

    terms: Union[Tuple[Var, Var],
                 Tuple[Tuple[Var, int], Tuple[Var, int]],                            
                 Tuple[Lit,...]]
    """
    Contains the terms of the constraint.

    The kind of constraint will have to match the types of terms to be
    successfully interpreted. The possibles types are the following:

    -`Tuple[Var, Var]`: 2 boolean variables. For `EQ` and `NEQ` constraints.

    -`Tuple[Tuple[Var, int], Tuple[Var, int]]`: 2 integer "atoms". An integer\
        "atom" is a variable + a constant (integer) offset. For `LEQ`, `LT`, `GEQ`,\
        `GT`, `EQ`, `NEQ` constraints.
        
    -`Tuple[Lit,...]`: any number of literals. For `OR`, `AND`, `IMPLY` constraints.\
        IMPLY constraints require excatly two literals, however.
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
    @classmethod
    def leq(cls,
        var_left: Var,
        offset_left: int,
        var_right: Var,
        offset_right: int,
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" constraint expression for the\
            constraint `var_left+offset_left <= var_right+offset_right`.
        """
        return ConstrExpr(ConstrExpr.Kind.LEQ, ((var_left, offset_left),
                                                (var_right, offset_right)))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def lt(cls,
        var_left: Var,
        offset_left: int,
        var_right: Var,
        offset_right: int,
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" constraint expression for the\
            `var_left+offset_left < var_right+offset_right`.
        """
        return ConstrExpr(ConstrExpr.Kind.LT, ((var_left, offset_left),
                                               (var_right, offset_right)))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def geq(cls,
        var_left: Var,
        offset_left: int,
        var_right: Var,
        offset_right: int,
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" constraint expression for the\
            `var_left+offset_left >= var_right+offset_right`.
        """
        return ConstrExpr(ConstrExpr.Kind.GEQ, ((var_left, offset_left),
                                                (var_right, offset_right)))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def gt(cls,
        var_left: Var,
        offset_left: int,
        var_right: Var,
        offset_right: int,
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" constraint expression for the\
            `var_left+offset_left > var_right+offset_right`.
        """
        return ConstrExpr(ConstrExpr.Kind.GT, ((var_left, offset_left),
                                               (var_right, offset_right)))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def eq(cls,
        terms: Tuple[Var, Var] | Tuple[Tuple[Var, int], Tuple[Var, int]],
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" constraint expression for the constraint\
                `terms[0][0]+terms[0][1] == terms[1][0]+terms[1][1]` if 2 integer atoms are given.                
            A "high-level" constraint expression for the constraint\
                `terms[0] == terms[1]` if 2 boolean variables are given.
        """
        return ConstrExpr(ConstrExpr.Kind.EQ, terms)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def neq(cls,
        terms: Tuple[Var, Var] | Tuple[Tuple[Var, int], Tuple[Var, int]],
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" constraint expression for the constraint\
                `terms[0][0]+terms[0][1] != terms[1][0]+terms[1][1]` if 2 integer atoms are given.                
            A "high-level" constraint expression for the constraint\
                `terms[0] != terms[1]` if 2 boolean variables are given.
        """
        return ConstrExpr(ConstrExpr.Kind.NEQ, terms)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def or_(cls,
        terms: Tuple[Lit,...],
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" constraint expression for the constraint `terms[0] | ... | terms[n]`.
        """
        return ConstrExpr(ConstrExpr.Kind.OR, terms)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def and_(cls,
        terms: Tuple[Lit,...]
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" constraint expression for the constraint `terms[0] & ... & terms[n]`.
        """
        return ConstrExpr(ConstrExpr.Kind.AND, terms)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def imply(cls,
        terms: Tuple[Lit, Lit],
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" constraint expression for the constraint `terms[0] => terms[1]`.
        """
        return ConstrExpr(ConstrExpr.Kind.IMPLY, terms)

#################################################################################
# "ELEMENTARY" CONSTRAINT EXPRESSIONS
#################################################################################

class ElemConstrExpr(NamedTuple):
    """
    Represents a "low-level" or "elementary" constraint to be used internally
    by the solver. They are integrated to the solver during processing / interpretation
    of "high-level" constraints.

    Warning:
        No errors will be raised if an incorrect / inconsistent / incompatible\
            instantiation is made (i.e. constraint type and terms are inconsistent).\
            However, errors may be raised during further processing, if the\
            expression cannot be interpreted.
    """
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Kind(Enum):
        LIT = auto()
        OR = auto()
        AND = auto()
        MAX_DIFFERENCE = auto() # TODO controllable ? contingent ?
# TODO        LINEAR = auto()
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    kind: Kind
    """Represents the type or kind of constraint."""

    terms: Union[Lit,
                 Tuple[Lit,...],
                 Tuple[Var, Var, int]]
    """
    Contains the terms of the constraint.

    The kind of constraint will have to match the types of terms to be
    successfully interpreted. The possibles types are the following:

    -`Lit`: 1 literal. For LIT constraints. (but `OR` and `AND` as well).

    -`Tuple[Lit,...]`: any number of literals. For `OR` and `AND` constraints.
        
    -`Tuple[Var, Var, int]`: For `MAX_DIFFERENCE` constraints (`target - source <= weight`).
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @property
    def negated(self) -> ElemConstrExpr:
        """The negated elementary constraint expression."""

        match self.kind, self.terms:

            case ElemConstrExpr.Kind.LIT, Lit() as lit:
                return ElemConstrExpr(ElemConstrExpr.Kind.LIT, lit.negated)

            case ElemConstrExpr.Kind.OR, [Lit(), *_] as lits:
                return ElemConstrExpr(ElemConstrExpr.Kind.AND, tuple(lit.negated for lit in lits))

            case ElemConstrExpr.Kind.AND, [Lit(), *_] as lits:
                return ElemConstrExpr(ElemConstrExpr.Kind.OR, tuple(lit.negated for lit in lits))

            case (ElemConstrExpr.Kind.MAX_DIFFERENCE,
                  (Var() as from_var, Var() as to_var, int() as max_diff)
            ):
                return ElemConstrExpr(ElemConstrExpr.Kind.MAX_DIFFERENCE,
                                      (to_var, from_var, -max_diff-1))
            case _:
                raise ValueError("ElemConstrExpr could not be interpreted: negation failed.")

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_int_atoms_leq(cls,
        var_left: Var,
        offset_left: int,
        var_right: Var,
        offset_right: int,
    ) -> ElemConstrExpr:
        """
        TODO
        """

        offset_diff = offset_right - offset_left

        if var_left == var_right:
            if offset_diff >= 0:
                return ElemConstrExpr.from_lit(TRUE_LIT)
            else:
                return ElemConstrExpr.from_lit(FALSE_LIT)
        
        elif var_right == ZERO_VAR:
            return ElemConstrExpr.from_lit(Lit.leq(var_left, offset_diff))

        elif var_left == ZERO_VAR:
            return ElemConstrExpr.from_lit(Lit.geq(var_right, -offset_diff))

        else:
            return ElemConstrExpr.from_max_diff(var_left, var_right, offset_diff)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_lit(cls,
        literal: Lit,
    ) -> ElemConstrExpr:
        """
        TODO
        """
        return ElemConstrExpr(ElemConstrExpr.Kind.LIT, literal)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_lits_simplify_or(cls,
        literals: Sequence[Lit],
    ) -> ElemConstrExpr:
        """
        TODO
        """

        if len(literals) == 0:
            return ElemConstrExpr.from_lit(FALSE_LIT)

        tightened_literals = tighten_literals(literals)

        if len(tightened_literals) == 1:
            return ElemConstrExpr.from_lit(tightened_literals[0])

        elif are_tightened_literals_tautological(tightened_literals):
            return ElemConstrExpr.from_lit(TRUE_LIT)

        return ElemConstrExpr(ElemConstrExpr.Kind.OR, tightened_literals)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_lits_simplify_and(cls,
        literals: Sequence[Lit]
    ) -> ElemConstrExpr:
        """
        TODO
        """

        if len(literals) == 0:
            return ElemConstrExpr.from_lit(TRUE_LIT)

        tightened_neg_literals = tighten_literals(tuple(lit.negated
                                                        for lit in literals))
        if len(tightened_neg_literals) == 1:
            return ElemConstrExpr.from_lit(tightened_neg_literals[0].negated)

        elif are_tightened_literals_tautological(tightened_neg_literals):
            return ElemConstrExpr.from_lit(FALSE_LIT)

        return ElemConstrExpr(ElemConstrExpr.Kind.AND, tuple(lit.negated
                                                        for lit in tightened_neg_literals))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_max_diff(cls,
        var_from: Var,
        var_to: Var,
        max_diff: int,
    ) -> ElemConstrExpr:
        """
        TODO
        """
        return ElemConstrExpr(ElemConstrExpr.Kind.MAX_DIFFERENCE, (var_from, var_to, max_diff))

#################################################################################
