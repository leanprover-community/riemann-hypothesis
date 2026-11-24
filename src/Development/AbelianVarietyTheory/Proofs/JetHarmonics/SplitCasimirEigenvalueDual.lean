module

public import Formalism.RealPlaceAnalysis.StatementE
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LastComatrixRowInvertsDual
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDualStandardRel
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL

namespace GlobalTheory

theorem splitCasimir_eigenvalue_dual : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (m : Fin (n + 1) → ℂ), GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ w v, qdet E w v = (∏ j, (w + m j)) • v) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → ∀ (lam : ℂ) (x : (PiLp 2 (fun _ : Fin (n + 1) => V))), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + (n : ℂ) := by
  intro V _ _ _ n E Et Om m hrel hunit hdet hEt hOm lam x hx hxe
  obtain ⟨-, -, -, hcomm⟩ := tensor_dual_standard_rel V n E Et Om hrel hunit hEt hOm
  obtain ⟨K, hK, -⟩ := lastComatrixRow_inverts_dual V n E Om m hrel hdet hOm
  have key : ∀ z : PiLp 2 (fun _ : Fin (n + 1) => V), Om z = lam • z →
      z (Fin.last n) ≠ 0 → ∃ j, lam = m j + (n : ℂ) := by
    intro z hz hzl
    have h0 := hK ((n : ℂ) - lam) z
    have hzero : ((n : ℂ) - lam - (n : ℂ)) • z + Om z = 0 := by
      rw [hz, ← add_smul]
      simp
    rw [hzero, map_zero] at h0
    have hprod : (∏ j, ((n : ℂ) - lam + m j)) = 0 := by
      rcases (smul_eq_zero.mp h0.symm) with h | h
      · exact h
      · exact absurd h hzl
    obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hprod
    exact ⟨j, by linear_combination -hj⟩
  by_cases hl : x (Fin.last n) = 0
  · have hc : ∃ c, x c ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      apply hx
      ext c
      simp [hne c]
    obtain ⟨c, hc⟩ := hc
    apply key (Et c (Fin.last n) x)
    · have h1 := congrArg (fun f => f x) (hcomm c (Fin.last n))
      simp only [Module.End.mul_apply] at h1
      rw [h1, hxe, map_smul]
    · rw [hEt, hl, map_zero]
      simpa using hc
  · exact key x hxe hl

end GlobalTheory
