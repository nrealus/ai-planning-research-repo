"""
This module defines the basic, fundamental building blocks used in the project.
"""

from __future__ import annotations

#################################################################################

from typing import List, NamedTuple, Sequence, Tuple

#################################################################################
# DOC: OK 23/10/23
#################################################################################

class Var(NamedTuple):
    """Represents a variable."""

    var_id: int

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

ZERO_VAR = Var(0)
"""
A special instance of `Var` whose domain will be assumed to be the single value 0.
"""

#################################################################################
# DOC: OK 23/10/23
#################################################################################

class SignedVar(NamedTuple):
    """
    Represents a so-called 'signed variable', which is a positive or negative view on a `Var`.
    
    The positive (resp. negative) signed variable for variable `var` is
    defined as `SignedVar(var, True)` (resp. `SignedVar(var, False)`).
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    var: Var
    """The `SignedVar`'s variable."""

    sign: bool
    """
    The `SignedVar`'s sign.
    
    True stands for the + sign (positive signed variable), and
    False for the - sign (negative signed variable).
    """

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @property
    def opposite(self) -> SignedVar:    # TODO: "opp" ?
        """The `SignedVar`'s opposite `SignedVar` (same variable, opposite sign)."""
        return SignedVar(self.var, not self.sign)

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
# DOC: OK 23/10/23
#################################################################################

class Bound(int):
    """
    Represents an upper bound of a `SignedVar`.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def __neg__(self) -> Bound:
        return Bound(-int(self))

    def __add__(self,
        other_bound: Bound
    ) -> Bound:
        return Bound(int(self)+other_bound)

    def __sub__(self,
        other_bound: Bound
    ) -> Bound:
        return Bound(int(self)-other_bound)

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    def is_stronger_than(self,
        other_bound: Bound,
    ) -> bool:
        """        
        Returns:
            Whether this bound is stronger than `other_bound` (i.e. less than or equal to it).
        """
        return self <= other_bound

#################################################################################
# DOC: OK 23/10/23
#################################################################################

class Lit(NamedTuple):
    """
    Represents a literal on a `SignedVar`, i.e. an expression `[svar <= b]`
    where `svar` is a `SignedVar` and `b` is a `Bound`.

    Implicitly, a literal on a `SignedVar` represents a literal on a `Var`.
    Indeed the literal `[var <= ub]` is equivalent to `[+var <= ub]`, where `var` is
    a `Var` and `+var` is a positive `SignedVar`. Likewise, `[var >= lb]` is equivalent
    to `[-var <= -lb]`, where `var` is a `Var` and `-var` is a negative `SignedVar`.
    """
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    signed_var: SignedVar
    """The `Lit`'s signed variable."""

    bound: Bound
    """The `Lit`'s bound."""
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @property
    def neg(self) -> Lit:
        """The `Lit`'s negation (i.e. negated `Lit`)."""
        return Lit(self.signed_var.opposite, -Bound(self.bound-1))
    
    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def leq(cls,
        var: Var,
        ub: int     
    ) -> Lit:
        """
        Syntactic sugar for `Lit(SignedVar.plus(var), Bound(ub))`,
        which represents the `[var <= ub]` literal.
        """
        return Lit(SignedVar.plus(var), Bound(ub))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

    @classmethod
    def geq(cls,
        var: Var,
        lb: int     
    ) -> Lit:
        """
        Syntactic sugar for `Lit(SignedVar.minus(var), Bound(-lb))`, which
        represents the `[var >= lb]` literal.
        """
        return Lit(SignedVar.minus(var), Bound(-lb))

    # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
        
    def entails(self,
        other_literal: Lit,
    ) -> bool:
        """
        Returns:
            Whether this literal entails `other_literal` \
                (i.e. it has the same signed variable and a stronger bound).
        """
        return (self.signed_var == other_literal.signed_var
                and self.bound.is_stronger_than(other_literal.bound))

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

TRUE_LIT = Lit.leq(ZERO_VAR, 0)
"""
A special "True" (or tautology) literal.

Relies on the fact that the value of the special variable `ZERO_VAR` will always be 0.
"""

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #

FALSE_LIT = TRUE_LIT.neg
"""
A special "False" (or contradiction) literal.

Is the negation of the True literal, which corresponds
to the `[ZERO_VAR >= 1]` (i.e. `[-ZERO_VAR <= -1]`) literal.
"""

#################################################################################
# DOC: OK 23/10/23
#################################################################################
 
def simplify_lits_disjunction(
    literals: Sequence[Lit]
) -> Tuple[Lit,...]:
        """
        Returns:
            A simplification of the disjunction composed of `literals`. \
            The simplified disjunction's literals are sorted (in lexicographic \
            order, as tuples) and only the weakest literal for each signed variable is kept.
        """

        lits: List[Lit] = sorted(literals)
        n = len(lits)
        i = 0
        j = 0
        while i < n-1:
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

def is_lits_disjunction_tautological(
    literals: Sequence[Lit]
) -> bool:
    """
    Returns:
        Whether the disjunction composed of `literals` is tautological \
            (i.e. is always true because it contains literals \
            `[var <= a]` and `[var >= b]` with `b <= a`).

    Warning:
        Assumes the disjunction is in "simplified form", i.e. its literals are sorted
        (in lexicographic order) and they're all on different signed variables.

        It is the caller's responsibility to make sure that the disjunction is
        indeed in "simplified form". A disjunction of literals can be simplified
        using `simplify_lits_disjunction`.

    Raises:
        ValueError: If the disjunction is empty (i.e. contains no literals).
        ValueError: If the disjunction is not in "simplified form".
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
            raise ValueError(("The disjunction is not in simplified form (i.e. ",
                                "literals are not sorted or there was two or more ",
                                "literals on the same signed variable)."))

            # TODO CHECK IF WE MEET THE "TRUE" / TAUTOLOGY LITERAL ?

        if literals[i].signed_var.opposite == literals[i+1].signed_var:
            # TODO/FIXME: use a function instead of - directly ?
            # but is_stronger_than isn't really suitable, is it ?
            # indeed, these bounds are of different types. one
            # is a lower bound, the other an upper one.
            if literals[i].bound - literals[i+1].bound <= 0:
                return True
        i += 1

    return False

#################################################################################
# DOC: OK 23/10/23
#################################################################################
# 
# class LitsDisjunction(Tuple[Lit,...]):
#     """Represents a disjunctive set of literals (aka disjunction of literals, aka disjunction)."""
# 
#     # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
#     @property
#     def simplified(self) -> LitsDisjunction:
#         """
#         Returns:
#             A simplified disjunction. The simplification sorts the literals \
#                 (as tuples, in lexicographic order) and only keeps the \
#                 weakest literal for each signed variable.
#         """
# 
#         lits: List[Lit] = sorted(self)
#         n = len(lits)
#         i = 0
#         j = 0
#         while i < n-1:
#             # Because the literals are now lexicographically sorted,
#             # we know that if two literals are on the same signed
#             # variable, the weaker one is necessarily the next one.
#             if lits[i].entails(lits[i+1]):
#                 lits.pop(i)
#                 j += 1
#             else:
#                 i += 1
# 
#         return LitsDisjunction(lits)
# 
#     # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
# #    @property
#     def is_tautological(self) -> bool:
#         """
#         Returns:
#             Whether the disjunction is tautological (i.e. is always true because \
#                 it contains literals `[var <= a]` and `[var >= b]` with `b <= a`).
# 
#         Warning:
#             Assumes the disjunction is in simplified form, i.e. its literals are sorted \
#                 (in lexicographic order) they're all on different signed variables. \
#                 A simplified disjunction can be obtained using `simplified`.
# 
#         Raises:
#             ValueError: If the disjunction is empty (i.e. contains no literals).
#             ValueError: If the disjunction is not in simplified form.
#         """
# 
#         n = len(self)
# 
#         if n == 0:
#             raise ValueError(("Attempt to check whether an empty set of literals is tautological. "
#                               "Technically, an empty set of literals is indeed tautological. However, "
#                               "at no point do we want a set of literals passed to this method "
#                               "to be empty, so we raise an error to further enforce that."))
#         i = 0
#         while i < n-1:
# 
#             if not (self[i] < self[i+1]
#                     and self[i].signed_var != self[i+1].signed_var
#             ):
#                 raise ValueError(("The disjunction is not in simplified form (i.e. ",
#                                   "literals are not sorted or there was two or more ",
#                                   "literals on the same signed variable)."))
# 
#              # TODO CHECK IF WE MEET THE "TRUE" / TAUTOLOGY LITERAL ?
# 
#             if self[i].signed_var.opposite == self[i+1].signed_var:
#                 # TODO/FIXME: use a function instead of - directly ?
#                 # but is_stronger_than isn't really suitable, is it ?
#                 # indeed, these bounds are of different types. one
#                 # is a lower bound, the other an upper one.
#                 if self[i].bound - self[i+1].bound <= 0:
#                     return True
#             i += 1
# 
#         return False
# 
#################################################################################
# 
#################################################################################
# 
# class LitsDisjunctiveSet(): # TODO: rename into Minimal Disjunctive Set ?
# 
#     def __init__(self,
#         lits: Sequence[Lit],
#     ):
#         self._lits_dict: Dict[SignedVar, Bound] = {}
#         for lit in lits:
#             self.insert(lit)
# 
#     # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
#     def insert(self,
#         lit: Lit
#     ) -> None:
#         if (lit.signed_var not in self._lits_dict
#             or self._lits_dict[lit.signed_var].is_stronger_than(lit.bound)
#         ):
#             self._lits_dict[lit.signed_var] = lit.bound
# 
#     # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
#     def remove(self,
#         lit: Lit
#     ) -> None:
#         self.insert(lit.neg)
# 
#     # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
#     def is_tautological(self) -> bool:
#         
#         for signed_var, bound in self._lits_dict.items():
#             if signed_var.opposite in self._lits_dict:
#                 if bound + self._lits_dict[signed_var.opposite] <= 0:
#                     return True
#         return False
# 
#     # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
#     @property
#     def as_sorted_tuple(self) -> Tuple[Lit, ...]:
#         return tuple(sorted(Lit(signed_var, bound) for signed_var, bound in self._lits_dict.items()))
# 
#################################################################################
# 
#################################################################################
# 
# class LitsConjunctiveSet():
# 
#     def __init__(self,
#         lits: Sequence[Lit],
#     ):
#         self._lits_dict: Dict[SignedVar, Bound] = {}
#         for lit in lits:
#             self.insert(lit)
# 
#     # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
#     def insert(self,
#         lit: Lit
#     ) -> None:
#         if (lit.signed_var not in self._lits_dict
#             or lit.bound.is_stronger_than(self._lits_dict[lit.signed_var])
#         ):
#             self._lits_dict[lit.signed_var] = lit.bound
# 
#     # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
#     def remove(self,
#         lit: Lit
#     ) -> None:
#         if lit.signed_var in self._lits_dict:
#             self._lits_dict[lit.signed_var] = Bound(lit.bound+1)
# 
#     # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
#     def is_contradictory(self) -> bool:
#         
#         for signed_var, bound in self._lits_dict.items():
#             if signed_var.opposite in self._lits_dict:
#                 if bound + self._lits_dict[signed_var.opposite] >= 0:
#                     return True
#         return False
# 
#     # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # #
# 
#     @property
#     def as_sorted_tuple(self) -> Tuple[Lit, ...]:
#         return tuple(sorted(Lit(signed_var, bound) for signed_var, bound in self._lits_dict.items()))
# 
#################################################################################
# DOC: TODO
#################################################################################

class BoolAtom(NamedTuple):
    lit: Lit

class IntAtom(NamedTuple):
    var: Var
    offset_cst: int

class FixedPointAtom(NamedTuple):
    num_int_atom: IntAtom
    denom: int

class SymbAtom(NamedTuple):
    int_view_atom: IntAtom  # TODO ?

Atom = BoolAtom | IntAtom | FixedPointAtom | SymbAtom