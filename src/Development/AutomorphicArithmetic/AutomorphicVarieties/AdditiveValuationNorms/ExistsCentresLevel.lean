module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.DetBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Growth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ImportsFurther
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.LteNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.NormVal
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperTheory.V UpperTheory.V.PropA

namespace UpperTheory.V.PropA

variable {l : ℕ} [Fact l.Prime] {X : Type} [AddCommGroup X] [Module ℤ_[l] X]

theorem twLen_le_growth {R c : ℕ} {γ : Module.End ℤ_[l] X} {u : ℤ_[l]} (hX : GenBy l R X) (hγ : Unip γ) (hu : IsLevel l u c)
    (e m : ℕ) : twLen γ u e m ≤ twLen γ u e (jZero l R) + ((R * (m - jZero l R) : ℕ) : ℕ∞) := by
  have h1 := (lteNorm l u c hu).2.1
  have hd : (l : ℤ_[l]) ∣ u ^ e - 1 := h1.trans (by simpa using sub_dvd_pow_sub_pow u 1 e)
  exact growth l X R _ hX (twist l X γ _ hd hγ) m

theorem exists_centres_level {R c : ℕ} (γ : Module.End ℤ_[l] X) {u : ℤ_[l]} (hX : GenBy l R X) (hu : IsLevel l u c) (j : ℕ) :
    ∃ s : Fin R → ℤ_[l], ∀ e : ℕ, twLen γ u e j ≤ ∑ i, (((j + c : ℕ) : ℕ∞) + vl l (s i - e)) := by
  obtain ⟨S, hS⟩ := lift l X R (γ ^ l ^ j) hX
  obtain ⟨s, hs⟩ := detBound l u c hu j R S
  refine ⟨s, fun e => ?_⟩
  have hpow : (u ^ e • γ) ^ l ^ j = (u ^ l ^ j) ^ e • γ ^ l ^ j := by
    rw [smul_pow, ← pow_mul, ← pow_mul, mul_comm]
  show cokLen ((u ^ e • γ) ^ l ^ j - 1) ≤ _
  rw [hpow]
  exact (hS _).trans (hs e)

theorem exists_centres {R c : ℕ} {γ : Module.End ℤ_[l] X} {u : ℤ_[l]} (hX : GenBy l R X) (hγ : Unip γ) (hu : IsLevel l u c) :
    ∃ s : Fin R → ℤ_[l], ∀ e m : ℕ,
      twLen γ u e m ≤ ∑ i, (((max m (jZero l R) + c : ℕ) : ℕ∞) + vl l (s i - e)) := by
  obtain ⟨s, hs⟩ := exists_centres_level γ hX hu (jZero l R)
  refine ⟨s, fun e m => ?_⟩
  refine (twLen_le_growth hX hγ hu e m).trans ?_
  have hm : max m (jZero l R) + c = (jZero l R + c) + (m - jZero l R) := by omega
  have key : ∑ i, (((max m (jZero l R) + c : ℕ) : ℕ∞) + vl l (s i - e))
      = ∑ i, (((jZero l R + c : ℕ) : ℕ∞) + vl l (s i - e)) + ((R * (m - jZero l R) : ℕ) : ℕ∞) := by
    rw [hm]
    simp only [Nat.cast_add, Nat.cast_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [key]
  gcongr
  exact hs e

theorem vl_le_of_norm {x : ℤ_[l]} {B : ℕ} (h : (l : ℝ) ^ (-(B : ℤ)) ≤ ‖x‖) : vl l x ≤ B := by
  have h' : ∏ _i : Fin 1, ((l : ℝ) ^ B)⁻¹ * ‖(1 : ℤ_[l])‖ ≤ ‖x‖ := by
    simpa [zpow_neg, zpow_natCast] using h
  have := normVal l 1 B x (fun _ => 1) h'
  simpa [vl] using this

theorem exists_centres_norm {R c : ℕ} {γ : Module.End ℤ_[l] X} {u : ℤ_[l]} (hX : GenBy l R X) (hγ : Unip γ)
    (hu : IsLevel l u c) : ∃ s : Fin R → ℤ_[l], ∀ e m B : ℕ, (∀ i, (l : ℝ) ^ (-(B : ℤ)) ≤ ‖s i - e‖) →
      twLen γ u e m ≤ ((R * (max m (jZero l R) + c + B) : ℕ) : ℕ∞) := by
  obtain ⟨s, hs⟩ := exists_centres hX hγ hu
  refine ⟨s, fun e m B hB => (hs e m).trans ?_⟩
  calc ∑ i, (((max m (jZero l R) + c : ℕ) : ℕ∞) + vl l (s i - e))
        ≤ ∑ _i : Fin R, (((max m (jZero l R) + c + B : ℕ) : ℕ∞)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Nat.cast_add _ B]
          gcongr
          exact vl_le_of_norm (hB i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]

end UpperTheory.V.PropA
