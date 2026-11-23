module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.CobPull

theorem cob1_subst_eq_pull2_of_isHom_formal : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), ∀ (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (φ : Fin d → MvPowerSeries (Fin d) R), (∀ i, constantCoeff (μ i) = 0) → (∀ i, constantCoeff (ν i) = 0) → IsHom μ ν φ → ∀ f : MvPowerSeries (Fin d) R, cob1 μ (subst φ f) = pull2 φ (cob1 ν f) := by
  intro R _ d μ ν φ hμ hν hφ f
  have hp : HasSubst φ := hasSubst_of_constantCoeff_zero hφ.const
  have hX : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hu : ∀ j, constantCoeff (inL (φ j)) = 0 := fun j => by
    unfold inL
    rw [SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]
  have hv : ∀ j, constantCoeff (inR (φ j)) = 0 := fun j => by
    unfold inR
    rw [SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]
  obtain ⟨hL, hR, hAS, -, -, hsub, -, -⟩ :=
    SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (fun j => inL (φ j))
      (fun j => inR (φ j)) hu hv
  unfold pull2 cob1
  rw [(hAS _ _).2, (hAS _ _).2, hL, hR, hsub d ν hν f]
  have e1 : subst μ (subst φ f) = subst (fun j => at2 (ν j) (fun j => inL (φ j)) (fun j => inR (φ j))) f := by
    rw [subst_comp_subst_apply hp (hasSubst_of_constantCoeff_zero hμ)]
    congr 1
    funext j
    exact hφ.hom j
  have e2 : inL (subst φ f) = subst (fun j => inL (φ j)) f := by
    unfold inL
    rw [subst_comp_subst_apply hp hX]
  have e3 : inR (subst φ f) = subst (fun j => inR (φ j)) f := by
    unfold inR
    rw [subst_comp_subst_apply hp hY]
  rw [e1, e2, e3]

end GlobalTheory.Katz.CobPull
