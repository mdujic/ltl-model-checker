#!/usr/bin/env python3
# -*- coding: utf-8 -*-
#
# This file is part of ltlf2dfa.
#
# ltlf2dfa is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# ltlf2dfa is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with ltlf2dfa.  If not, see <https://www.gnu.org/licenses/>.
#

"""This module contains the implementation of Linear Temporal Logic on finite traces."""

import re
from abc import ABC, abstractmethod
from typing import Any, List, Optional

from base import (
    AtomicFormula,
    AtomSymbol,
    BinaryOperator,
    Formula,
    UnaryOperator,
)

from helpers import new_var
from symbols import OpSymbol, Symbols


class LTLfFormula(Formula, ABC):
    """A class for the LTLf formula."""

    def to_nnf(self) -> "LTLfFormula":
        """Convert an LTLf formula in NNF."""
        return self

    @abstractmethod
    def negate(self) -> "LTLfFormula":
        """Negate the formula."""

    def __repr__(self):
        """Get the representation."""
        return self.__str__()


    def to_ldlf(self):
        """
        Tranform the formula into an equivalent LDLf formula.

        :return: an LDLf formula.
        """

    

class LTLfUnaryOperator(UnaryOperator[LTLfFormula], LTLfFormula, ABC):
    """A unary operator for LTLf."""


class LTLfBinaryOperator(BinaryOperator[LTLfFormula], LTLfFormula, ABC):
    """A binary operator for LTLf."""


class LTLfAtomic(AtomicFormula, LTLfFormula):
    """Class for LTLf atomic formulas."""

    name_regex = re.compile(r"[a-z][a-z0-9_]*")

    def negate(self):
        """Negate the formula."""
        return LTLfNot(self)

    def find_labels(self) -> List[AtomSymbol]:
        """Find the labels."""
        return PLAtomic(self.s).find_labels()

    

class LTLfTrue(LTLfAtomic):
    """Class for the LTLf True formula."""

    def __init__(self):
        """Initialize the formula."""
        super().__init__(Symbols.TRUE.value)

    def negate(self):
        """Negate the formula."""
        return LTLfFalse()

    def find_labels(self) -> List[AtomSymbol]:
        """Find the labels."""
        return list()

    

class LTLfFalse(LTLfAtomic):
    """Class for the LTLf False formula."""

    def __init__(self):
        """Initialize the formula."""
        super().__init__(Symbols.FALSE.value)

    def negate(self):
        """Negate the formula."""
        return LTLfTrue()

    def find_labels(self) -> List[AtomSymbol]:
        """Find the labels."""
        return list()



class LTLfNot(LTLfUnaryOperator):
    """Class for the LTLf not formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.NOT.value

    def to_nnf(self) -> LTLfFormula:
        """Transform to NNF."""
        if not isinstance(self.f, AtomicFormula):
            return self.f.negate().to_nnf()
        else:
            return self

    def negate(self) -> LTLfFormula:
        """Negate the formula."""
        return self.f



class LTLfAnd(LTLfBinaryOperator):
    """Class for the LTLf And formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.AND.value

    def negate(self) -> LTLfFormula:
        """Negate the formula."""
        return LTLfOr([f.negate() for f in self.formulas])



class LTLfOr(LTLfBinaryOperator):
    """Class for the LTLf Or formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.OR.value

    def negate(self) -> LTLfFormula:
        """Negate the formula."""
        return LTLfAnd([f.negate() for f in self.formulas])




class LTLfImplies(LTLfBinaryOperator):
    """Class for the LTLf Implication formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.IMPLIES.value

    def negate(self) -> LTLfFormula:
        """Negate the formula."""
        return self.to_nnf().negate()

    def to_nnf(self) -> LTLfFormula:
        """Transform to NNF."""
        first, second = self.formulas[0:2]
        final_formula = LTLfOr([LTLfNot(first).to_nnf(), second.to_nnf()])
        for subformula in self.formulas[2:]:
            final_formula = LTLfOr(
                [LTLfNot(final_formula).to_nnf(), subformula.to_nnf()]
            )
        return final_formula




class LTLfEquivalence(LTLfBinaryOperator):
    """Class for the LTLf Equivalente formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.EQUIVALENCE.value

    def to_nnf(self) -> LTLfFormula:
        """Transform to NNF."""
        fs = self.formulas
        pos = LTLfAnd(fs)
        neg = LTLfAnd([LTLfNot(f) for f in fs])
        res = LTLfOr([pos, neg]).to_nnf()
        return res

    def negate(self) -> LTLfFormula:
        """Negate the formula."""
        return self.to_nnf().negate()


class LTLfNext(LTLfUnaryOperator):
    """Class for the LTLf Next formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.NEXT.value

    def to_nnf(self) -> LTLfFormula:
        """Transform to NNF."""
        return LTLfNext(self.f.to_nnf())

    def negate(self) -> LTLfFormula:
        """Negate the formula."""
        return LTLfWeakNext(self.f.negate())



class LTLfWeakNext(LTLfUnaryOperator):
    """Class for the LTLf Weak Next formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.WEAK_NEXT.value

    def to_nnf(self) -> LTLfFormula:
        """Transform to NNF."""
        return LTLfWeakNext(self.f.to_nnf())

    def negate(self) -> LTLfFormula:
        """Negate the formula."""
        return LTLfNext(self.f.negate())
    
class LTLfWeakUntil(LTLfBinaryOperator):
    """Class for the LTLf Weak Until formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.UNTIL.value

    def to_nnf(self):
        """Transform to NNF."""
        return LTLfUntil([f.to_nnf() for f in self.formulas])


class LTLfUntil(LTLfBinaryOperator):
    """Class for the LTLf Until formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.UNTIL.value

    def to_nnf(self):
        """Transform to NNF."""
        return LTLfUntil([f.to_nnf() for f in self.formulas])

    def negate(self):
        """Negate the formula."""
        return LTLfRelease([f.negate() for f in self.formulas])



class LTLfRelease(LTLfBinaryOperator):
    """Class for the LTLf Release formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.RELEASE.value

    def to_nnf(self):
        """Transform to NNF."""
        return LTLfRelease([f.to_nnf() for f in self.formulas])

    def negate(self):
        """Negate the formula."""
        return LTLfUntil([f.negate() for f in self.formulas])



class LTLfEventually(LTLfUnaryOperator):
    """Class for the LTLf Eventually formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.EVENTUALLY.value

    def to_nnf(self) -> LTLfFormula:
        """Transform to NNF."""
        return LTLfUntil([LTLfTrue(), self.f])

    def negate(self) -> LTLfFormula:
        """Negate the formula."""
        return self.to_nnf().negate()



class LTLfAlways(LTLfUnaryOperator):
    """Class for the LTLf Always formula."""

    @property
    def operator_symbol(self) -> OpSymbol:
        """Get the operator symbol."""
        return Symbols.ALWAYS.value

    def to_nnf(self) -> LTLfFormula:
        """Transform to NNF."""
        return LTLfRelease([LTLfFalse(), self.f.to_nnf()])

    def negate(self) -> LTLfFormula:
        """Negate the formula."""
        return self.to_nnf().negate()




class LTLfLast(LTLfFormula):
    """Class for the LTLf Last formula."""

    def to_nnf(self) -> LTLfFormula:
        """Transform to NNF."""
        return LTLfAnd([LTLfWeakNext(LTLfFalse()), LTLfNot(LTLfEnd())]).to_nnf()

    def negate(self) -> LTLfFormula:
        """Negate the formula."""
        return self.to_nnf().negate()

    def find_labels(self) -> List[AtomSymbol]:
        """Find the labels."""
        return list()

    def _members(self):
        return (Symbols.LAST.value,)

    def __str__(self):
        """Get the string representation."""
        return Symbols.LAST.value

class LTLfEnd(LTLfFormula):
    """Class for the LTLf End formula."""

    def find_labels(self) -> List[AtomSymbol]:
        """Find the labels."""
        return list()

    def _members(self):
        return (Symbols.END.value,)

    def to_nnf(self) -> LTLfFormula:
        """Transform to NNF."""
        return LTLfAlways(LTLfFalse()).to_nnf()

    def negate(self) -> LTLfFormula:
        """Negate the formula."""
        return self.to_nnf().negate()

    def __str__(self):
        """Get the string representation."""
        return "_".join(map(str, self._members()))
