module

public import Formalism.RealPlaceAnalysis.StatementB
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Formalism.REAL

namespace GlobalTheory

theorem highestWeight_tensor_standard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (θ : Fin (n + 1) → ℂ) (lam : ℂ) (y : (PiLp 2 (fun _ : Fin (n + 1) => V))), (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → y ≠ 0 → IsHW Et θ y → Om y = lam • y → ∃ c, y c ≠ 0 ∧ IsHW E (fun a => θ a - if a = c then 1 else 0) (y c) ∧ lam = θ c - 1 - ((c : ℕ) : ℂ) := by
  classical
  intro V _ _ _ n E Et Om θ lam y hEt hOm hy hw hlam
  obtain ⟨h1, h2⟩ := hw
  have hne : (Finset.univ.filter (fun c => y c ≠ 0)).Nonempty := by
    by_contra h
    apply hy
    ext c
    by_contra hc
    exact h ⟨c, by simpa using hc⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image _ id hne
  have hc0 : y c ≠ 0 := by simpa using hc
  have hz : ∀ d, c < d → y d = 0 := by
    intro d hd
    by_contra h
    exact absurd (hmax d (by simpa using h)) (not_le.mpr hd)
  have hup : ∀ a b, a < b → ∀ e, E a b (y e) = - if e = a then y b else 0 := by
    intro a b hab e
    have h := hEt a b y e
    have h0 : Et a b y = 0 := h2 a b hab
    rw [h0] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have hdiag : ∀ a, E a a (y c) = (θ a - if a = c then 1 else 0) • y c := by
    intro a
    have h := hEt a a y c
    have h0 : Et a a y = θ a • y := h1 a
    rw [h0] at h
    have h' : E a a (y c) = θ a • y c - if c = a then y a else 0 := by
      rw [eq_sub_iff_add_eq, ← h]; rfl
    rw [h']
    by_cases hca : c = a
    · subst hca; simp [sub_smul]
    · simp [hca, Ne.symm hca]
  have hraise : ∀ a b, a < b → E a b (y c) = 0 := by
    intro a b hab
    rw [hup a b hab c]
    by_cases hca : c = a
    · subst hca; simp [hz b hab]
    · simp [hca]
  refine ⟨c, hc0, ⟨hdiag, hraise⟩, ?_⟩
  have hterm : ∀ d, E d c (y d) =
      ((if d = c then θ c - 1 else 0) - if d < c then 1 else 0 : ℂ) • y c := by
    intro d
    rcases lt_trichotomy d c with h | h | h
    · rw [hup d c h d]; simp [h, h.ne]
    · subst h; rw [hdiag]; simp
    · simp [hz d h, h.ne', not_lt.mpr h.le]
  have hsum : lam • y c = (θ c - 1 - ((c : ℕ) : ℂ)) • y c := by
    have h := hOm y c
    rw [hlam] at h
    have h' : lam • y c = ∑ d, E d c (y d) := h
    rw [h', Finset.sum_congr rfl (fun d _ => hterm d), ← Finset.sum_smul,
      Finset.sum_sub_distrib]
    congr 2
    · simp
    · rw [Finset.sum_boole]
      have : Finset.univ.filter (fun d => d < c) = Finset.Iio c := by ext d; simp
      rw [this, Fin.card_Iio]
  exact smul_left_injective ℂ hc0 hsum

end GlobalTheory
