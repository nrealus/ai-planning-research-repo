"""
This module defines both "high-level" and "low-level" constraint expressions.

"High-level" (or "natural") constraint expressions (`ConstrExpr`) are specified
by the user and fed to the solver. "Low-level" (or "elementary") constraint
expressions (`ElemConstrExpr`) are used internally by the solver, and are obtained
by the decomposing "high-level" constraint expressions.
"""

from __future__ import annotations

#################################################################################
# FILE CONTENTS:
# - HIGH LEVEL CONSTRAINT EXPRESSIONS
# - LOW LEVEL CONSTRAINT EXPRESSIONS
#################################################################################

from enum import Enum, auto
from typing import NamedTuple, Sequence, Tuple, Union

from src.fundamentals import (FALSE_LIT, TRUE_LIT, ZERO_VAR, Lit, Var, 
                              simplify_lits_disjunction, is_lits_disjunction_tautological,
                              BoolAtom, IntAtom, FracAtom, SymbAtom)

#################################################################################
# DOC: OK 25/10/23
#################################################################################

class ConstrExpr(NamedTuple):
    """
    Represents a "high-level" or "natural" constraint, specified by the user.
    They are preprocessed / interpreted by the solver into "low-level" constraints,
    which it uses internally.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    class Kind(Enum):
        LEQ = auto()
        LT = auto()
        EQ = auto()
        NEQ = auto()
        OR = auto()
        AND = auto()
        IMPLY = auto()
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    kind: Kind

    terms: Union[Tuple[BoolAtom, BoolAtom],
                 Tuple[IntAtom, IntAtom],
                 Tuple[FracAtom, FracAtom],
                 Tuple[SymbAtom, SymbAtom],
                 Tuple[Lit,...],
                 Tuple[Lit, Lit]]

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def leq(cls,
        int_or_frac_atoms_pair: Tuple[IntAtom, IntAtom] | Tuple[FracAtom, FracAtom]
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" expression for the "<=" (less than or equal to, aka leq) constraint, \
                between two `IntAtom`s or two `FracAtom`s.

        Raises:
            ValueError: If a pair of `FracAtom`s has different denominators.
        """
        match int_or_frac_atoms_pair:

            case IntAtom(), IntAtom():
                return ConstrExpr(ConstrExpr.Kind.LEQ, int_or_frac_atoms_pair)

            case FracAtom(_, denom_left), FracAtom(_, denom_right):
                if denom_left != denom_right:
                    raise ValueError("`FracAtom`s are required to have the same denominator to be comparable.")
                return ConstrExpr(ConstrExpr.Kind.LEQ, int_or_frac_atoms_pair)
            
            case _:
                assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def lt(cls,
        int_or_frac_atoms_pair: Tuple[IntAtom, IntAtom] | Tuple[FracAtom, FracAtom]
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" expression for the "<" (strictly less than, aka lt) constraint, \
                between two `IntAtom`s or two `FracAtom`s.

        Raises:
            ValueError: If a pair of `FracAtom`s has different denominators.
        """
        match int_or_frac_atoms_pair:

            case IntAtom(), IntAtom():
                return ConstrExpr(ConstrExpr.Kind.LT, int_or_frac_atoms_pair)

            case FracAtom(_, denom_left), FracAtom(_, denom_right):
                if denom_left != denom_right:
                    raise ValueError("`FracAtom`s are required to have the same denominator to be comparable.")
                return ConstrExpr(ConstrExpr.Kind.LT, int_or_frac_atoms_pair)
            
            case _:
                assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def eq(cls,
        bool_int_frac_or_sym_atoms_pair: Union[Tuple[BoolAtom, BoolAtom],
                                               Tuple[IntAtom, IntAtom],
                                               Tuple[FracAtom, FracAtom],
                                               Tuple[SymbAtom, SymbAtom]]
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" expression for the "=" (equality, aka eq) constraint, \
                between two `BoolAtom`s, two `IntAtom`s, two `FracAtom`s, or two `SymbAtom`s.

        Raises:
            ValueError: If a pair of `FracAtom`s has different denominators, \
                or a pair of `SymbAtom`s has different types.                
        """
        match bool_int_frac_or_sym_atoms_pair:

            case BoolAtom(), BoolAtom():
                return ConstrExpr(ConstrExpr.Kind.EQ, bool_int_frac_or_sym_atoms_pair)

            case IntAtom(), IntAtom():
                return ConstrExpr(ConstrExpr.Kind.EQ, bool_int_frac_or_sym_atoms_pair)

            case FracAtom(_, denom_left), FracAtom(_, denom_right):
                if denom_left != denom_right:
                    raise ValueError("`FracAtom`s are required to have the same denominator to be comparable.")
                return ConstrExpr(ConstrExpr.Kind.EQ, bool_int_frac_or_sym_atoms_pair)
            
            case SymbAtom(_, symb_type_left), SymbAtom(_, symb_type_right):
#               TODO !!!
#                if (not symb_type_left.is_subtype_of(symb_type_right, ...)
#                    and not symb_type_right.is_subtype_of(symb_type_left, ...)
#                ):
#                    raise ValueError("`SymbAtom`s are required to have the same symbol type to be comparable.")
                return ConstrExpr(ConstrExpr.Kind.EQ, bool_int_frac_or_sym_atoms_pair)
            
            case _:
                assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def neq(cls,
        bool_int_frac_or_sym_atoms_pair: Union[Tuple[BoolAtom, BoolAtom],
                                               Tuple[IntAtom, IntAtom],
                                               Tuple[FracAtom, FracAtom],
                                               Tuple[SymbAtom, SymbAtom]]
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" expression for the "!=" (inequality, aka neq) constraint, \
                between two `BoolAtom`s, two `IntAtom`s, two `FracAtom`s, or two `SymbAtom`s.
        
        Raises:
            ValueError: If a pair of `FracAtom`s has different denominators, \
                or a pair of `SymbAtom`s has different types.     
        """
        match bool_int_frac_or_sym_atoms_pair:

            case BoolAtom(), BoolAtom():
                return ConstrExpr(ConstrExpr.Kind.NEQ, bool_int_frac_or_sym_atoms_pair)

            case IntAtom(), IntAtom():
                return ConstrExpr(ConstrExpr.Kind.NEQ, bool_int_frac_or_sym_atoms_pair)

            case FracAtom(_, denom_left), FracAtom(_, denom_right):
                if denom_left != denom_right:
                    raise ValueError("`FracAtom`s are required to have the same denominator to be comparable.")
                return ConstrExpr(ConstrExpr.Kind.NEQ, bool_int_frac_or_sym_atoms_pair)
            
            case SymbAtom(_, symb_type_left), SymbAtom(_, symb_type_right):
                if symb_type_left != symb_type_right:
                    raise ValueError("`SymbAtom`s are required to have the same symbol type to be comparable.")
                return ConstrExpr(ConstrExpr.Kind.NEQ, bool_int_frac_or_sym_atoms_pair)
            
            case _:
                assert False

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def or_(cls,
        literals: Tuple[Lit,...],
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" expression for the "or" (disjunction) constraint, on a non empty set of `Lit`s.

        Raises:
            ValueError: If `literals` is empty.
        """
        if len(literals) == 0:
            raise ValueError("A non empty set of literals is required to build a high-level 'or' constraint expression.")

        return ConstrExpr(ConstrExpr.Kind.OR, literals)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def and_(cls,
        literals: Tuple[Lit,...]
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" expression for the "and" (conjunction) constraint, on a non empty set of `Lit`s.

        Raises:
            ValueError: If `literals` is empty.
        """
        if len(literals) == 0:
            raise ValueError("A non empty set of literals is required to build a high-level 'and' constraint expression.")

        return ConstrExpr(ConstrExpr.Kind.AND, literals)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def imply(cls,
        literals_pair: Tuple[Lit, Lit],
    ) -> ConstrExpr:
        """
        Returns:
            A "high-level" expression for the "imply" (implication) constraint `literals_pair[0] => literals_pair[1]`.
        """
        return ConstrExpr(ConstrExpr.Kind.IMPLY, literals_pair)

#################################################################################
# DOC: OK 25/10/23
#################################################################################

class ElemConstrExpr(NamedTuple):
    """
    Represents a "low-level" or "elementary" constraint to be used internally
    by the solver. They are integrated to the solver during processing / interpretation
    of "high-level" constraints.
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

    terms: Union[Lit,
                 Tuple[Lit,...],
                 Tuple[Var, Var, int]]

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @property
    def neg(self) -> ElemConstrExpr:
        """
        Returns:
            The negated "low-level" constraint expression.
        """

        match self.kind, self.terms:

            case ElemConstrExpr.Kind.LIT, Lit() as lit:
                return ElemConstrExpr(ElemConstrExpr.Kind.LIT, lit.neg)

            case ElemConstrExpr.Kind.OR, [Lit(), *_] as lits:
                return ElemConstrExpr(ElemConstrExpr.Kind.AND, tuple(lit.neg for lit in lits))

            case ElemConstrExpr.Kind.AND, [Lit(), *_] as lits:
                return ElemConstrExpr(ElemConstrExpr.Kind.OR, tuple(lit.neg for lit in lits))

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
        int_atom_left: IntAtom,
        int_atom_right: IntAtom,
    ) -> ElemConstrExpr:
        """
        Returns:
            A "low-level" constraint expression interpreting a "less than or equal" \
                comparison between two `IntAtom`s.
        """

        var_left: Var = int_atom_left.var
        var_right: Var = int_atom_right.var

        offset_diff: int = int_atom_right.offset_cst - int_atom_left.offset_cst

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
            return ElemConstrExpr.from_vars_max_diff(var_left, var_right, offset_diff)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_lit(cls,
        literal: Lit,
    ) -> ElemConstrExpr:
        """
        Returns:
            A "low-level" constraint expression interpreting the entailment \
                of the single literal `literal`.
        """
        return ElemConstrExpr(ElemConstrExpr.Kind.LIT, literal)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_lits_or(cls,
        literals: Sequence[Lit],
    ) -> ElemConstrExpr:
        """
        Returns:
            A "low-level" constraint expression interpreting the disjunction of the given literals.
        """
        if len(literals) == 0:
            return ElemConstrExpr.from_lit(FALSE_LIT)

        simplified_lits_disjunction = simplify_lits_disjunction(literals)

        if len(simplified_lits_disjunction) == 1:
            return ElemConstrExpr.from_lit(simplified_lits_disjunction[0])

        elif is_lits_disjunction_tautological(simplified_lits_disjunction):
            return ElemConstrExpr.from_lit(TRUE_LIT)

        return ElemConstrExpr(ElemConstrExpr.Kind.OR, simplified_lits_disjunction)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_lits_and(cls,
        literals: Sequence[Lit]
    ) -> ElemConstrExpr:
        """
        Returns:
            A "low-level" constraint expression interpreting the conjunction of the given literals.
        """
        if len(literals) == 0:
            return ElemConstrExpr.from_lit(TRUE_LIT)

        simplified_neg_lits_disjunction = simplify_lits_disjunction([lit.neg for lit in literals])

        if len(simplified_neg_lits_disjunction) == 1:
            return ElemConstrExpr.from_lit(simplified_neg_lits_disjunction[0].neg)

        elif is_lits_disjunction_tautological(simplified_neg_lits_disjunction):
            return ElemConstrExpr.from_lit(FALSE_LIT)

        return ElemConstrExpr(ElemConstrExpr.Kind.AND, tuple(lit.neg for lit in simplified_neg_lits_disjunction))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def from_vars_max_diff(cls,
        var_from: Var,
        var_to: Var,
        max_diff: int,
    ) -> ElemConstrExpr:
        """
        Returns:
            A "low-level" constraint expression interpreting `var_to - var_from <= max_diff`.
        """
        return ElemConstrExpr(ElemConstrExpr.Kind.MAX_DIFFERENCE, (var_from, var_to, max_diff))
