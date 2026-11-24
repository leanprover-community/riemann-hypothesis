module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.AWFront

theorem sub_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have e : SimplexCategory.subinterval (n := N) 0 N h = 𝟙 _ := by
    ext i
    simp [SimplexCategory.subinterval]
  unfold Sx.sub
  rw [e, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem ev_of_front {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {S : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj S) I n) (β : Cochain ((chains R).obj S) J m) (γ : Cochain ((chains R).obj S) K k)
    (hγ : μ.IsAW hk α β γ)
    (hα : ∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S s U), 0 < s → ev α s t h U x = 0)
    (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx S N U) :
    ev γ N w h U x = μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega)))
      (ev β N _ rfl U x) := by
  have key : ∀ (s : ℤ) (hs : s = n) (H : s + (-(N : ℤ) + m) = w) (h1 : -((0 : ℕ) : ℤ) + n = s),
      μ.mul U s (-(N : ℤ) + m) w H (ev α 0 s h1 U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) =
        μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
    rintro s rfl H h1
    rfl
  have gen : ∀ (p : ℕ), p = 0 → ∀ (H : -(p : ℤ) + n + (-((N - p : ℕ) : ℤ) + m) = w) (h1 : 0 + p ≤ N)
      (h2 : p + (N - p) ≤ N),
      (m * (p : ℤ)).negOnePow • μ.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w H
        (ev α p _ rfl U (x.sub 0 p h1)) (ev β (N - p) _ rfl U (x.sub p (N - p) h2)) =
      μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
    rintro p rfl H h1 h2
    have e1 : (m * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
    rw [e1, one_smul]
    have e2 : x.sub 0 (N - 0) h2 = x := sub_full x h2
    rw [e2]
    exact key _ (by simp) H rfl
  rw [hγ N w h U x, Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => ?_), add_zero]
  · exact gen _ (by simp) _ _ _
  · rw [hα (i.succ : ℕ) _ rfl U _ (by simp), map_zero, LinearMap.zero_apply, smul_zero]

end GlobalTheory.AWFront
