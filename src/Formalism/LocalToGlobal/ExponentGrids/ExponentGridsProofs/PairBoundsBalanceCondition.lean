import Mathlib
import Formalism.LocalToGlobal.ExponentGrids.IntegerShiftClosedExponent
import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.ArithmeticBoundCyclicTwo
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols SPer IndefNum IndefCore)
open Formalism.L2.GlobalTheoryTheory (Arith.Cst Arith.Lev Arith.Lev.admitted Arith.sg Arith.elt Arith.eltBar Arith.pOf Arith.EatT)

noncomputable section

namespace Formalism.AtG

namespace UnitPeriodBounds

open PlacesLyingOver Formalism.DivisionValues.PlaceSumConjugation

variable {K : Type} [Field K] [NumberField K]


end UnitPeriodBounds

open PlacesLyingOver UnitPeriodBounds Formalism.DivisionValues.PlaceSumConjugation Formalism.DivisionValues.ValuationRepresentative


end Formalism.AtG
