module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.ConjEquidistrib

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric
open scoped nonZeroDivisors Pointwise


open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates in
theorem fixesK_conjEmb_iff (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) :
    FixesK D M (conjEmb M ρ) ↔ ¬ FixesK D M ρ := by
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp D.host.K.val.toRingHom
  let σM : D.host.K →+* M := σ.codRestrict M hm
  have hsq := D.host.sqd_sq
  let b : D.host.K :=
    ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hb : b ^ 2 = -(D.host.d : D.host.K) := by
    apply Subtype.ext
    simpa using hsq
  have hall : ∀ ψ : D.host.K →+* ℂ, ψ b ^ 2 = -(D.host.d : ℂ) := fun ψ => by
    rw [← map_pow, hb, map_neg, map_natCast]
  have hcj : ∀ ψ : D.host.K →+* ℂ, (starRingEnd ℂ) (ψ b) = -ψ b := fun ψ => by
    have h1 : (ψ b) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
      rw [hall, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;>
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal] <;> ring
  have hne : σ b ≠ 0 := by
    intro h0
    have := hall σ
    rw [h0] at this
    have hd : (0 : ℂ) ≠ -(D.host.d : ℂ) := by
      rw [ne_eq, eq_comm, neg_eq_zero, Nat.cast_eq_zero]
      exact D.host.hyp.2.1.ne_zero
    exact hd (by simpa using this)
  have key : ∀ ρ' : M →ₐ[ℚ] ℂ, ρ' (σM b) = σ b → FixesK D M ρ' := fun ρ' h x y hy => by
    have : ((ρ' : M →+* ℂ).comp σM).toRatAlgHom = σ.toRatAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K)
        (s := {D.host.sqd}) rfl fun x hx => ?_
      obtain rfl : x = _ := hx
      exact h
    have h2 : ρ' (σM x) = σ x := DFunLike.congr_fun this x
    have hyx : y = σM x := Subtype.ext hy
    rw [hyx]
    exact h2
  have back : ∀ ρ' : M →ₐ[ℚ] ℂ, FixesK D M ρ' → ρ' (σM b) = σ b := fun ρ' h => h b (σM b) rfl
  have h1 : ρ (σM b) ^ 2 = σ b ^ 2 := (hall ((ρ : M →+* ℂ).comp σM)).trans (hall σ).symm
  constructor
  · intro hc hf
    have e1 := back _ hc
    have e2 := back _ hf
    rw [conjEmb_apply, e2, hcj] at e1
    exact hne (by linear_combination -e1 / 2)
  · intro hf
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact absurd (key ρ h) hf
    · refine key _ ?_
      rw [conjEmb_apply, h, map_neg, hcj, neg_neg]

theorem fixK_of_fixesK (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ)
    (hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M) (h : GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates.FixesK D M ρ) :
    Formalism.MainNotions.StandardLatticesGL3.FixK D M ρ := fun a => by
  refine ⟨hm a, ?_⟩
  unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM
  rw [dite_eq_left (hm a)]
  exact h a _ rfl

open GlobalTheory.IndefiniteRowSideFullHecke.EquidistributedConjugates

end GlobalTheory.ConjEquidistrib
