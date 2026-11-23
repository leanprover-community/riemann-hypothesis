module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
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

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem linearIndependent_laurentMonomial :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (s : Finset ι) (n : ℤ) (v : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} → LocalizedModule.Away (xProd R s) (MvPolynomial ι R)), (∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0) → v a = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1)) → LinearIndependent R v := by
  intro ι _ _ R _ s n v hv
  rw [linearIndependent_iff']
  intro T g hg j hj
  let k : ℕ := T.sup fun a => Finset.univ.sup fun i => (a.1 i).natAbs
  let m : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} → (ι →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm fun i => (a.1 i + if i ∈ s then (k : ℤ) else 0).toNat
  have hm : ∀ a ∈ T, ∀ i, (m a i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0 := by
    intro a ha i
    have hk : (a.1 i).natAbs ≤ k :=
      (Finset.le_sup (f := fun i => (a.1 i).natAbs) (Finset.mem_univ i)).trans
        (Finset.le_sup (f := fun a : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} =>
          Finset.univ.sup fun i => (a.1 i).natAbs) ha)
    refine Int.toNat_of_nonneg ?_
    split_ifs with hi
    · omega
    · simpa using a.2.2 i hi
  have hinj : ∀ a ∈ T, m a = m j → a = j := by
    intro a ha e
    refine Subtype.ext (funext fun i => ?_)
    have h1 := hm a ha i
    have h2 := hm j hj i
    rw [e, h2] at h1
    exact (add_right_cancel h1).symm
  have h0 : awayFrac (MvPolynomial ι R) (xProd R s) k
      (∑ a ∈ T, g a • monomial (m a) (1 : R)) = 0 := by

    rw [map_sum, ← hg]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hv a k (m a) (hm a ha), LinearMap.map_smul_of_tower]
  have h1 := congrArg (AddMonoidAlgebra.coeff · (m j))
    ((map_eq_zero_iff _ (awayFrac_injective (xProd_smul_injective s) k)).1 h0)
  rw [coeff_sum, Finset.sum_eq_single j, MvPolynomial.coeff_smul, coeff_monomial, if_pos rfl] at h1
  · simpa using h1
  · intro a ha hne
    rw [MvPolynomial.coeff_smul, coeff_monomial, if_neg fun e => hne (hinj a ha e), smul_zero]
  · exact fun h => absurd hj h

end GlobalTheory
