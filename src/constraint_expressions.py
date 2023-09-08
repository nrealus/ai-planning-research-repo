from __future__ import annotations

#################################################################################

from typing import NamedTuple, Tuple, Union
from enum import Enum, auto

from fundamentals import (
    Var, ZERO_VAR,
    Lit, TRUE_LIT, FALSE_LIT,
    tighten_literals, are_tightened_literals_tautological,
)

#################################################################################
#################################################################################
#                                   CONTENTS:
# - ("NATURAL") CONSTRAINT EXPRESSIONS
# - ELEMENTARY CONSTRAINT EXPRESSIONS
#################################################################################
#################################################################################

#################################################################################
# ("NATURAL") CONSTRAINT EXPRESSIONS
#################################################################################

class ConstrExpr(NamedTuple):
    """
    Represents a constraint in a "front-facing" / "front-end" / "natural" view for the user.

    No errors will be raised if an incorrect / inconsistent / incompatible
    instantiation is made. (i.e. constraint type and terms are inconsistent)

    However, an error may be raised during processing, if the expression could not 
    be interpreted (because it is incorrect).
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

    terms: Union[Tuple[Var, Var],                           # - 2 boolean variables
                 Tuple[Tuple[Var, int], Tuple[Var, int]],   # - 2 integer (numeric) "atoms":
                                                            #   (variables + constant offsets)
                 Tuple[Lit,...]]                            # - n literals
                                                            #   (strictly 2 for "IMPLY" constraints)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
    @classmethod
    def leq(cls,
        var_left: Var,
        offset_left: int,
        var_right: Var,
        offset_right: int,
    ) -> ConstrExpr:
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
        return ConstrExpr(ConstrExpr.Kind.GT, ((var_left, offset_left),
                                               (var_right, offset_right)))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def eq(cls,
        terms: Tuple[Var, Var] | Tuple[Tuple[Var, int], Tuple[Var, int]],
    ) -> ConstrExpr:
        return ConstrExpr(ConstrExpr.Kind.EQ, terms)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def neq(cls,
        terms: Tuple[Var, Var] | Tuple[Tuple[Var, int], Tuple[Var, int]],
    ) -> ConstrExpr:
        return ConstrExpr(ConstrExpr.Kind.NEQ, terms)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def or_(cls,
        terms: Tuple[Lit,...],
    ) -> ConstrExpr:
        return ConstrExpr(ConstrExpr.Kind.OR, terms)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def and_(cls,
        terms: Tuple[Lit,...]
    ) -> ConstrExpr:
        return ConstrExpr(ConstrExpr.Kind.AND, terms)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def imply(cls,
        terms: Tuple[Lit, Lit],
    ) -> ConstrExpr:
        return ConstrExpr(ConstrExpr.Kind.IMPLY, terms)

#################################################################################
# "ELEMENTARY" CONSTRAINT EXPRESSIONS
#################################################################################

class ElemConstrExpr(NamedTuple):
    """
    Represents a constraint in a "back-facing" / "back-end" view, for internal use
    by the solver.

    Elementary constraints expressions are obtained and integrated to the solver
    during processing of "natural" constraint expressions.

    No errors will be raised if an incorrect / inconsistent / incompatible
    instantiation is made. (i.e. constraint type and terms are inconsistent)

    However, an error may be raised during processing if the expression could not
    be interpreted (because it is incorrect).
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

    terms: Union[Lit,                   # for LIT constraints
                 Tuple[Lit,...],        # for OR and AND constraints
                 Tuple[Var, Var, int]]  # for MAX_DIFFERENCE constraints

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_int_atoms_leq(cls,
        var_left: Var,
        offset_left: int,
        var_right: Var,
        offset_right: int,
    ) -> ElemConstrExpr:

        offset_diff = offset_right - offset_left

        if var_left == var_right:
            if 0 <= offset_diff:
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
        return ElemConstrExpr(ElemConstrExpr.Kind.LIT, literal)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_lits_tighten_and_simplify_or(cls,
        literals: Tuple[Lit,...],
    ) -> ElemConstrExpr:

        tightened_literals = tighten_literals(literals)

        if are_tightened_literals_tautological(tightened_literals):
            return ElemConstrExpr.from_lit(TRUE_LIT)

        elif len(tightened_literals) == 0:
            return ElemConstrExpr.from_lit(FALSE_LIT)

        elif len(tightened_literals) == 1:
            return ElemConstrExpr.from_lit(tightened_literals[0])

        return ElemConstrExpr(ElemConstrExpr.Kind.OR, tightened_literals)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
#
#    @classmethod
#    def or_from_lits(cls,
#        literals: Tuple[Lit,...],
#    ) -> ElemConstrExpr:
#        return ElemConstrExpr(ElemConstrExpr.Kind.OR, literals)
#
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_lits_and(cls,
        literals: Tuple[Lit,...]
    ) -> ElemConstrExpr:
        return ElemConstrExpr(ElemConstrExpr.Kind.AND, literals)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_max_diff(cls,
        var_from: Var,
        var_to: Var,
        max_diff: int,
    ) -> ElemConstrExpr:
        return ElemConstrExpr(ElemConstrExpr.Kind.MAX_DIFFERENCE, (var_from, var_to, max_diff))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def negation(self) -> ElemConstrExpr:

        match self.kind, self.terms:

            case ElemConstrExpr.Kind.LIT, Lit() as lit:
                return ElemConstrExpr.from_lit(lit.negation())

            case ElemConstrExpr.Kind.OR, [Lit(), *_] as lits:
                return ElemConstrExpr.from_lits_and(tuple(lit.negation() for lit in lits))

            case ElemConstrExpr.Kind.AND, [Lit(), *_] as lits:
                return ElemConstrExpr(ElemConstrExpr.Kind.OR, tuple(lit.negation() for lit in lits))

            case (ElemConstrExpr.Kind.MAX_DIFFERENCE,
                  (Var() as from_var, Var() as to_var, int() as max_diff)
            ):
                return ElemConstrExpr.from_max_diff(to_var, from_var, -max_diff-1)

            case _:
                raise ValueError("""ElemConstrExpr could not be interpreted: negation failed.""")

#################################################################################
