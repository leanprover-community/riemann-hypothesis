module

public import Formalism.PairingDivisors.StatementH
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
public import Formalism.PairingDivisors.StatementX

@[expose] public section

noncomputable section

open NumberField
open IsDedekindDomain
open Finset
open Formalism.PairingDivisionLocalBalance (wt HtLe meanInf)
open Formalism.HN (muMaxDef htMap)
open Formalism.DivisionValues
open Formalism.L2.Indef
open Formalism.L2.Indef.Tree

namespace Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

def NonArchimedeanDefectBound {K : Type} [Field K] [NumberField K] {ι : Type} (dl : Formalism.PairingDivisionLocalBalance.Pl K → ℝ) (zA zA' : ι → K) (B : ℝ) : Prop :=
  (∀ w, 0 ≤ dl w) ∧ (∀ F : Finset (Formalism.PairingDivisionLocalBalance.Pl K), ∑ w ∈ F, lw w * dl w ≤ B) ∧
    ∀ ij, zA ij ≠ 0 ∧ zA' ij ≠ 0 ∧
      ∀ w, -(3 * dl w) ≤ (vw w (zA ij) : ℝ) ∧ -(3 * dl w) ≤ (vw w (zA' ij) : ℝ)

end Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
