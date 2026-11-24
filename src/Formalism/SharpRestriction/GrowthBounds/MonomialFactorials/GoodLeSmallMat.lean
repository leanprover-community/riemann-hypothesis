module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.OrthCountOf
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.GoodCountMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset


open Classical in
def GoodLeSmallMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m : ℕ) (X Y : Fin n → Fin m → ℤ_[p]) (c : Fin m → ℚ_[p]) (D : ℤ),
    (∀ i j, ∑ a, (X i a : ℚ_[p]) * c a * (Y j a : ℚ_[p]) = if i = j then (p : ℚ_[p]) ^ D else 0) →
    n ≤ (Finset.univ.filter (fun a : Fin m => c a ≠ 0 ∧ (c a).valuation ≤ D)).card

theorem B_sum_left {p : ℕ} [Fact p.Prime] {σ ι : Type} (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (hsm : ∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (s : Finset ι) (g : ι → MvPolynomial σ ℚ_[p]) (v : MvPolynomial σ ℚ_[p]) :
    B (∑ i ∈ s, g i) v = ∑ i ∈ s, B (g i) v := by
  classical
  have h0 : B 0 v = 0 := by
    have := hsm 0 0 v
    simpa using this
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih => rw [Finset.sum_insert ha, hadd, ih, Finset.sum_insert ha]

theorem goodLeSmall_of (h : GoodLeSmallMat) : GoodLeSmall := by
  intro p _ σ B L W D _ _ hsm hadd hsy m f hf _ hspan horth
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p B L D
  have hcoord : ∀ v ∈ L, ∃ X : Fin m → ℤ_[p], ∑ a, X a • f a = v := by
    intro v hv
    rw [← hspan] at hv
    exact (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hv
  choose! X hX using hcoord
  have hsmZ : ∀ (c : ℤ_[p]) (u : MvPolynomial σ ℚ_[p]), c • u = (c : ℚ_[p]) • u :=
    fun c u => (algebraMap_smul ℚ_[p] c u).symm
  have hexp : ∀ v ∈ L, ∀ w, B v w = ∑ a, (X v a : ℚ_[p]) * B (f a) w := by
    intro v hv w
    conv_lhs => rw [← hX v hv]
    rw [B_sum_left B hsm hadd]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsmZ, hsm]
  have hfy : ∀ a j, B (f a) (y j) = (X (y j) a : ℚ_[p]) * B (f a) (f a) := by
    intro a j
    rw [hsy _ (hf a) _ (hy j), hexp _ (hy j)]
    rw [Finset.sum_eq_single a]
    · intro b _ hb
      rw [horth b a hb, mul_zero]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  exact h p _ m (fun i => X (x i)) (fun j => X (y j)) (fun a => B (f a) (f a)) D (fun i j => by
    rw [← hxy i j, hexp _ (hx i)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hfy]
    ring)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
