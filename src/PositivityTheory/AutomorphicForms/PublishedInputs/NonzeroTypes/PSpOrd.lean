module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spOrd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_one (n : ℕ) : ∑ _a : Fin n, (1 : ℕ) = n := by simp

theorem stdBlocks_one (n : ℕ) :
    (stdBlocks (fun _ : Fin n => 1) (sum_one n) : (Σ _ : Fin n, Fin 1) ≃ Fin n) =
      Equiv.sigmaUnique (Fin n) (fun _ => Fin 1) := by
  refine Equiv.ext fun x => ?_
  obtain ⟨a, i⟩ := x
  refine Fin.ext ?_
  rw [stdBlocks_val]
  simp

theorem isSmooth_detRep1 {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : IsSmooth (detRep (Fin 1) χ) :=
  (isSmooth_ofChar_iff _).2 (h.detChar (n := Fin 1))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hasFiniteLength_detRep1 (χ : kˣ →* ℂˣ) : HasFiniteLength (detRep (R := k) (Fin 1) χ) :=
  hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _)

theorem prin_sub_multi {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) :
    IsSubquotient (prinSeries χ)
      (multiProd (stdBlocks (fun _ : Fin n => 1) (sum_one n)) fun i => detRep (Fin 1) (χ i)) := by
  have h := GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ
  rw [← stdBlocks_one] at h
  exact h

end UpperTheory.TNZ.Grp.P_spOrd

namespace UpperTheory.TNZ.Grp

open UpperTheory.TNZ.Grp.P_spOrd GlobalTheory.LocGL.SupportRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

end UpperTheory.TNZ.Grp
