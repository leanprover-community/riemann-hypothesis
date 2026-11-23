module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenspacesOfSeparableMinpoly
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

namespace GlobalTheory.RegCommutant

theorem exists_not_commute_of_two_le_finrank {K E : Type} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (h : 2 ≤ Module.finrank K E) :
    ∃ S₁ S₂ : Module.End K E, S₁ * S₂ ≠ S₂ * S₁ := by
  let b := Module.finBasis K E
  let e := LinearMap.toMatrixAlgEquiv b
  let i0 : Fin (Module.finrank K E) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank K E) := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨e.symm (Matrix.single i0 i1 1), e.symm (Matrix.single i1 i0 1), ?_⟩
  intro hc
  have h2 := congrArg e hc
  simp only [map_mul, AlgEquiv.apply_symm_apply] at h2
  have h3 := congrFun (congrFun h2 i0) i0
  rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same] at h3
  simp [Matrix.single_apply, hne.symm] at h3

theorem finrank_le_natDegree_minpoly (K V : Type) [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : Module.End K V) (hs : (minpoly K T).Separable)
    (hc : ∀ a b : Module.End K V, Commute a T → Commute b T → Commute a b) :
    Module.finrank K V ≤ (minpoly K T).natDegree := by
  classical
  set f := minpoly K T with hf
  have hmon : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  obtain ⟨hsum, -⟩ := GlobalTheory.EigSum.finrank_eigenspaces_of_separable_minpoly K V T f hmon hs
    (minpoly.aeval K T) (fun g hg => minpoly.dvd K T hg)
  have hcard : f.roots.toFinset.card = f.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs)]
    exact ((IsAlgClosed.splits f).natDegree_eq_card_roots).symm
  by_contra hlt
  push_neg at hlt
  obtain ⟨μ, hμ, h2⟩ : ∃ μ ∈ f.roots.toFinset, 2 ≤ Module.finrank K (T.eigenspace μ) := by
    by_contra hno
    push_neg at hno
    have : ∑ z ∈ f.roots.toFinset, Module.finrank K (T.eigenspace z) ≤
        ∑ z ∈ f.roots.toFinset, 1 :=
      Finset.sum_le_sum fun z hz => Nat.lt_succ_iff.mp (hno z hz)
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at this
    omega
  have hroot : f.IsRoot μ := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hmon.ne_zero] at hμ; exact hμ
  set q := f /ₘ (Polynomial.X - Polynomial.C μ) with hq
  have hfq : (Polynomial.X - Polynomial.C μ) * q = f :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hqμ : q.eval μ ≠ 0 := by
    intro h0
    have hq' : (Polynomial.X - Polynomial.C μ) * (q /ₘ (Polynomial.X - Polynomial.C μ)) = q :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr h0
    obtain ⟨q2, hq2⟩ : ∃ q2, (Polynomial.X - Polynomial.C μ) * q2 = q := ⟨_, hq'⟩
    have hu : IsUnit (Polynomial.X - Polynomial.C μ) :=
      hs.squarefree _ ⟨q2, by rw [← hfq, ← hq2]; ring⟩
    exact Polynomial.not_isUnit_X_sub_C μ hu
  set c := q.eval μ with hc_def
  set Q := Polynomial.aeval T q with hQ
  set E := T.eigenspace μ with hE
  have hTQ : ∀ v, T (Q v) = μ • Q v := by
    intro v
    have h0 : Polynomial.aeval T ((Polynomial.X - Polynomial.C μ) * q) = 0 := by
      rw [hfq]; exact minpoly.aeval K T
    have h1 := congrArg (fun g : Module.End K V => g v) h0
    simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply,
      LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.zero_apply] at h1
    exact sub_eq_zero.mp h1
  have hQT : ∀ v, Q (T v) = T (Q v) := by
    intro v
    have h := congrArg (Polynomial.aeval T) (mul_comm q Polynomial.X)
    simp only [map_mul, Polynomial.aeval_X] at h
    exact congrArg (fun g : Module.End K V => g v) h
  have hQE : ∀ v, Q v ∈ E := by
    intro v
    rw [hE, Module.End.mem_eigenspace_iff]
    exact hTQ v
  have hQid : ∀ u ∈ E, Q u = c • u := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [hu0]
    · exact Module.End.aeval_apply_of_hasEigenvector ⟨hu, hu0⟩
  let π : V →ₗ[K] E := Q.codRestrict E hQE
  let ι : E →ₗ[K] V := E.subtype
  have hπι : ∀ x : E, π (ι x) = c • x := by
    intro x; apply Subtype.ext; simp [π, ι, hQid x.1 x.2]
  have hπT : ∀ v, π (T v) = μ • π v := by
    intro v; apply Subtype.ext; simp [π, hQT v, hTQ v]
  have hcomm : ∀ S : Module.End K E, Commute (ι ∘ₗ S ∘ₗ π) T := by
    intro S
    apply LinearMap.ext
    intro v
    have hm : T (S (π v) : V) = μ • (S (π v) : V) := Module.End.mem_eigenspace_iff.mp (S (π v)).2
    simp only [Module.End.mul_apply, LinearMap.comp_apply, hπT v, map_smul]
    simp [ι, hm]
  obtain ⟨S₁, S₂, hS⟩ := exists_not_commute_of_two_le_finrank h2
  have hab := hc _ _ (hcomm S₁) (hcomm S₂)
  apply hS
  apply LinearMap.ext
  intro w
  have h1 := congrArg (fun g : Module.End K V => g (ι (c⁻¹ • c⁻¹ • w))) hab.eq
  simp only [Module.End.mul_apply, LinearMap.comp_apply, map_smul, hπι, smul_smul] at h1
  apply Subtype.ext
  simpa [ι, mul_inv_cancel₀ hqμ, inv_mul_cancel₀ hqμ, mul_assoc, mul_left_comm] using h1

theorem natDegree_minpoly_eq_of_commutant_comm : ∀ (K : Type) [Field K] [IsAlgClosed K] (k : ℕ)
    (N : Matrix (Fin k) (Fin k) K), (minpoly K N).Separable →
    (∀ A B : Matrix (Fin k) (Fin k) K, Commute A N → Commute B N → Commute A B) →
    (minpoly K N).natDegree = k := by
  intro K _ _ k N hs hc
  have hmin : minpoly K (Matrix.toLin' N) = minpoly K N := Matrix.minpoly_toLin' N
  apply le_antisymm
  · calc (minpoly K N).natDegree ≤ N.charpoly.natDegree :=
          Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly N) (Matrix.charpoly_monic N).ne_zero
      _ = k := by rw [Matrix.charpoly_natDegree_eq_dim]; simp
  · have h := finrank_le_natDegree_minpoly K (Fin k → K) (Matrix.toLin' N) (hmin ▸ hs) ?_
    · simpa [hmin] using h
    · intro a b ha hb
      let e : Matrix (Fin k) (Fin k) K ≃ₐ[K] Module.End K (Fin k → K) := Matrix.toLinAlgEquiv'
      have hN : e.symm (Matrix.toLin' N) = N := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      have hA := ha.map e.symm
      have hB := hb.map e.symm
      rw [hN] at hA hB
      simpa only [AlgEquiv.apply_symm_apply] using (hc _ _ hA hB).map e

end GlobalTheory.RegCommutant
