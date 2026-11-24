module

public import Development.EtaleCohomology.KummerTheory.PlacePf
public import Mathlib.RingTheory.LocalRing.LocalSubring
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

namespace LateralTheory.KummerTheory

def PlaceGood (k K : Type) [Field k] [Field K] [Algebra k K] (A : LocalSubring K) : Prop :=
  (∀ c : k, algebraMap k K c ∈ A.toSubring) ∧
    ∀ a ∈ A.toSubring, ∃ c : k, a = algebraMap k K c ∨ (a - algebraMap k K c)⁻¹ ∉ A.toSubring

def PlaceZorn : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K],
  ∃ A : LocalSubring K, PlaceGood k K A ∧ ∀ B : LocalSubring K, A ≤ B → PlaceGood k K B → B ≤ A

def PlaceStep : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] (A : LocalSubring K),
  PlaceGood k K A → (∀ B : LocalSubring K, A ≤ B → PlaceGood k K B → B ≤ A) →
    ∀ x : K, x ∈ A.toSubring ∨ x⁻¹ ∈ A.toSubring

theorem PlaceEx_of (h1 : PlaceZorn) (h2 : PlaceStep) : PlaceEx := by
  intro k K _ _ _ _ _
  obtain ⟨A, hA, hmax⟩ := h1 k K
  have hv := h2 k K A hA hmax
  let T : ValuationSubring K := ⟨A.toSubring, hv⟩
  let σ : k →+* T := (algebraMap k K).codRestrict T (fun c => hA.1 c)
  refine ⟨T, σ, fun x => rfl, ?_⟩
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := hA.2 a a.2
  refine ⟨c, ?_⟩
  simp only [RingHom.comp_apply]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
  have hK : ((σ c : K) - (a : K)) * (w : K) = 1 := by
    have := congrArg (fun z : T => (z : K)) hw
    simpa using this
  rcases hc with h | h
  · have : (σ c : K) - (a : K) = 0 := by rw [h]; simp [σ]
    rw [this, zero_mul] at hK; exact zero_ne_one hK
  · apply h
    have hinv : ((σ c : K) - (a : K))⁻¹ = (w : K) := inv_eq_of_mul_eq_one_right hK
    have : ((a : K) - algebraMap k K c)⁻¹ = -(w : K) := by
      rw [← hinv, ← inv_neg, neg_sub]; rfl
    rw [this]; exact T.neg_mem _ w.2

end LateralTheory.KummerTheory
