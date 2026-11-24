module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DedekindFiniteTypeIdealCodimension
public import Mathlib.RingTheory.Norm.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLowDegreeCoordsModMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSquarefreePolyDistinctZerosOnCurve
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormDegreeBoundPolynomialCombination
public import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Int

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDegreeLtTwoCorrectionSimpleZero, Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearSystemMaximalDegreeFactorization

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDegreeLtTwoCorrectionSimpleZero =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDegreeLtTwoCorrectionSimpleZero", "h": "module\n\npublic import Mathlib.FieldTheory.IsAlgClosed.Basic\npublic import Mathlib.RingTheory.DedekindDomain.Basic\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DedekindFiniteTypeIdealCodimension\nimport Mathlib.Algebra.AffineMonoid.UniqueSums\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Finiteness.ModuleFinitePresentation\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.TotallySplit\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Polynomial

namespace GlobalTheory

theorem exists_deg_lt_two_correction_simple :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (P₀ : Ideal A) (w : A),
      P₀.IsMaximal → ∃ p : Fin n → k[X], (∀ i, (p i).degree < (2 : ℕ)) ∧
        w + ∑ i, p i • b i ∈ P₀ ∧ w + ∑ i, p i • b i ∉ P₀ ^ 2 := by
  intro k A _ _ _ _ _ _ _ _ _ _ n b P₀ w hP
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨φ, hφ⟩ := ((_root_.GlobalTheory.DedekindCodim.dedekind_finiteType_codim k A).2.1 P₀ hP).2
  set α : k := φ (algebraMap k[X] A X) with hα
  have hC : algebraMap k[X] A (C α) = algebraMap k A α := by
    rw [IsScalarTower.algebraMap_apply k k[X] A]; rfl
  have hlin : algebraMap k[X] A (X - C α) ∈ P₀ := by
    rw [hφ, map_sub, map_sub, hC, φ.commutes, ← hα]
    simp
  have hne : algebraMap k[X] A (X - C α) ≠ 0 := by
    intro h0
    have h1 : (X - C α) • (1 : A) = 0 := by rw [Algebra.smul_def, h0, zero_mul]
    have h3 : b.repr (1 : A) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]; exact one_ne_zero
    obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp h3
    have h4 := congrArg (fun a => b.repr a i) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h4
    exact mul_ne_zero (X_sub_C_ne_zero α) hi h4
  have hbot : P₀ ≠ ⊥ := fun h => hne (by rw [h] at hlin; simpa using hlin)
  have hlt := Ideal.pow_lt_self P₀ hbot hP.ne_top 2 le_rfl
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  set q : k[X] := (X - C α) ^ 2 with hq
  have hmon : q.Monic := (monic_X_sub_C α).pow 2
  have hqdeg : q.degree = (2 : ℕ) := by
    rw [hq, degree_pow, degree_X_sub_C]; rfl
  have hqmem : algebraMap k[X] A q ∈ P₀ ^ 2 := by
    rw [hq, map_pow]; exact Ideal.pow_mem_pow hlin 2
  let c : Fin n → k[X] := fun i => b.repr (π - w) i
  let p : Fin n → k[X] := fun i => c i %ₘ q
  let d : Fin n → k[X] := fun i => c i /ₘ q
  have hs : ∑ i, c i • b i = π - w := b.sum_repr (π - w)
  have h2 : ∑ i, c i • b i = ∑ i, p i • b i + algebraMap k[X] A q * ∑ i, d i • b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Algebra.smul_def, smul_smul, ← add_smul]
    exact congrArg (· • b i) (modByMonic_add_div (c i) q).symm
  have key : w + ∑ i, p i • b i = π - algebraMap k[X] A q * ∑ i, d i • b i := by
    linear_combination hs - h2
  have hM : algebraMap k[X] A q * ∑ i, d i • b i ∈ P₀ ^ 2 := Ideal.mul_mem_right _ _ hqmem
  refine ⟨p, fun i => ?_, ?_, ?_⟩
  · rw [← hqdeg]; exact degree_modByMonic_lt _ hmon
  · rw [key]; exact P₀.sub_mem hπP (Ideal.pow_le_self two_ne_zero hM)
  · intro h
    apply hπ2
    have : π = (w + ∑ i, p i • b i) + algebraMap k[X] A q * ∑ i, d i • b i := by
      rw [key]; ring
    rw [this]; exact (P₀ ^ 2).add_mem h hM

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDegreeLtTwoCorrectionSimpleZero =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearSystemMaximalDegreeFactorization =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearSystemMaximalDegreeFactorization", "h": "module\n\npublic import Mathlib.FieldTheory.IsAlgClosed.Basic\npublic import Mathlib.RingTheory.DedekindDomain.Basic\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDegreeLtTwoCorrectionSimpleZero\npublic import Mathlib.RingTheory.Norm.Defs\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLowDegreeCoordsModMul\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSquarefreePolyDistinctZerosOnCurve\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormDegreeBoundPolynomialCombination\npublic import Mathlib.LinearAlgebra.FreeModule.Norm\nimport Mathlib.Algebra.AffineMonoid.UniqueSums\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Polynomial

noncomputable section

namespace GlobalTheory.LinSys

section Bounded

variable {k A : Type} [Field k] [CommRing A] [Algebra k A] [Algebra k[X] A]
  [IsScalarTower k k[X] A]

theorem repr_smul_const {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (c : k) (f : A) (i : Fin n) :
    b.repr (c • f) i = C c * b.repr f i := by
  rw [← algebraMap_smul k[X] c f, map_smul, Finsupp.smul_apply, smul_eq_mul,
    Polynomial.algebraMap_eq]

def boundedIn {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) : Submodule k A where
  carrier := {f | f ∈ D ∧ ∀ i, (b.repr f i).natDegree ≤ d}
  zero_mem' := ⟨D.zero_mem, fun i => by simp⟩
  add_mem' := fun {f g} hf hg => ⟨D.add_mem hf.1 hg.1, fun i => by
    rw [map_add (f := _), Finsupp.add_apply]
    exact (natDegree_add_le _ _).trans (max_le (hf.2 i) (hg.2 i))⟩
  smul_mem' := fun c f hf => ⟨by rw [Algebra.smul_def]; exact D.mul_mem_left _ hf.1, fun i => by
    rw [repr_smul_const]
    exact (natDegree_C_mul_le _ _).trans (hf.2 i)⟩

def coeffMap {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) :
    boundedIn b D d →ₗ[k] (Fin n → Fin (d + 1) → k) where
  toFun f i j := (b.repr (f : A) i).coeff j
  map_add' f g := by ext i j; simp
  map_smul' c f := by ext i j; simp [repr_smul_const, coeff_C_mul]

theorem coeffMap_injective {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A) (d : ℕ) :
    Function.Injective (coeffMap b D d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  have h0 : ∀ i, b.repr (f : A) i = 0 := by
    intro i
    ext j
    by_cases hj : j ≤ d
    · have := congrFun (congrFun hf i) ⟨j, Nat.lt_succ_of_le hj⟩
      simpa [coeffMap] using this
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (f.2.2 i) (not_le.1 hj))]; simp
  have : (f : A) = 0 := by
    rw [← b.sum_repr (f : A)]; simp [h0]
  exact Subtype.ext this

instance finiteDimensional_boundedIn {n : ℕ} (b : Module.Basis (Fin n) k[X] A) (D : Ideal A)
    (d : ℕ) : FiniteDimensional k (boundedIn b D d) :=
  Module.Finite.of_injective (coeffMap b D d) (coeffMap_injective b D d)

end Bounded

theorem isCoprime_of_not_le {A : Type} [CommRing A] {M D : Ideal A} (hM : M.IsMaximal)
    (h : ¬ D ≤ M) : IsCoprime M D := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h'
  exact h (le_sup_right.trans (hM.eq_of_le h' le_sup_left).ge)

end GlobalTheory.LinSys


open GlobalTheory.LinSys in
theorem GlobalTheory.linear_system_setup : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ) (P₀ : Ideal A), 1 ≤ N → P₀.IsMaximal → ∃ (r : ℕ) (V : Submodule k A) (D : Ideal A) (Q : Fin r → Ideal A) (f₀ : A), (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) ∧ (∀ f ∈ V, f ≠ 0 → Module.finrank k (A ⧸ Ideal.span {f}) ≤ Module.finrank k (A ⧸ Ideal.span {f₀})) := by
  intro k A _ _ _ _ _ _ _ _ _ _ N P₀ hN hP
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set n := Module.finrank k[X] A
  let b : Module.Basis (Fin n) k[X] A := Module.finBasis k[X] A
  obtain ⟨c, lam, hdeg1, hdeg2⟩ := _root_.GlobalTheory.NormDegree.natDegree_norm_of_coord_degree k A n b
  obtain ⟨p, hp2, hpP, hpP2⟩ := _root_.GlobalTheory.exists_deg_lt_two_correction_simple k A n b P₀ (∑ i, (C (lam i) * X ^ 2) • b i) hP
  set f₁ : A := ∑ i, (C (lam i) * X ^ 2 + p i) • b i with hf₁def
  have hf₁eq : (∑ i, (C (lam i) * X ^ 2) • b i) + ∑ i, p i • b i = f₁ := by
    rw [hf₁def, ← Finset.sum_add_distrib]; simp [add_smul]
  rw [hf₁eq] at hpP hpP2
  obtain ⟨hf₁0, hf₁deg⟩ := hdeg2 2 p hp2
  obtain ⟨D, hD⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hpP)
  have hDP : ¬ D ≤ P₀ := by
    intro h
    apply hpP2
    have : Ideal.span {f₁} ≤ P₀ ^ 2 := by rw [hD, sq]; exact Ideal.mul_mono_right h
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  have hf₁D : f₁ ∈ D := by
    have : Ideal.span {f₁} ≤ D := hD ▸ Ideal.mul_le_right
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  set s := n * 2 + c with hs
  obtain ⟨q, r, Q, hqm, hqdeg, hQmax, hQinj, hf₁Q, hqQ⟩ := _root_.GlobalTheory.SquarefreeFibre.main k A f₁ s hf₁0
  set d := 2 + (M + 1) * s with hd
  have hspan : ∀ m : ℕ, Ideal.span {f₁ * algebraMap k[X] A (q ^ m)} = P₀ * D * ∏ i, Q i ^ m := by
    intro m
    rw [← Ideal.span_singleton_mul_span_singleton, hD, map_pow, ← Ideal.span_singleton_pow, hqQ,
      Finset.prod_pow]
  have hrepr₁ : ∀ i, b.repr f₁ i = C (lam i) * X ^ 2 + p i := by
    intro i; rw [hf₁def, b.repr_sum_self]
  have hdeg₁ : ∀ i, (b.repr f₁ i).natDegree ≤ 2 := by
    intro i
    rw [hrepr₁]
    exact (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _)
      (natDegree_le_iff_degree_le.2 (le_of_lt (hp2 i))))
  set f₀ : A := f₁ * algebraMap k[X] A (q ^ (M + 1)) with hf₀def
  have hf₀smul : f₀ = q ^ (M + 1) • f₁ := by rw [hf₀def, Algebra.smul_def, mul_comm]
  have hf₀0 : f₀ ≠ 0 := by
    rw [hf₀smul]; exact smul_ne_zero (pow_ne_zero _ hqm.ne_zero) hf₁0
  have hf₀V : f₀ ∈ boundedIn b D d := by
    refine ⟨D.mul_mem_right _ hf₁D, fun i => ?_⟩
    rw [hf₀smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    refine (natDegree_mul_le).trans ?_
    rw [hqm.natDegree_pow, hqdeg]
    have := hdeg₁ i
    omega
  have hnorm₁ : Algebra.norm k[X] f₁ ≠ 0 := Algebra.norm_ne_zero_iff.2 hf₁0
  have hf₀deg : (Algebra.norm k[X] f₀).natDegree = n * d + c := by
    rw [hf₀def, map_mul, Algebra.norm_algebraMap_of_basis b, Fintype.card_fin,
      natDegree_mul hnorm₁ (pow_ne_zero _ (pow_ne_zero _ hqm.ne_zero)), hf₁deg,
      natDegree_pow, hqm.natDegree_pow, hqdeg, hd, hs]
    ring
  refine ⟨r, boundedIn b D d, D, Q, f₀, ⟨inferInstance, fun v hv => hv.1, hQmax, hQinj,
    fun i h => hf₁Q i (h ▸ hpP), fun i h => hf₁Q i (h hf₁D), hDP, hf₀V, hf₀0, hspan (M + 1),
    ?_⟩, ?_⟩
  · intro u
    have hcop : IsCoprime (P₀ * ∏ i, Q i ^ M) D :=
      (isCoprime_of_not_le hP hDP).mul_left
        (IsCoprime.prod_left fun i _ => (isCoprime_of_not_le (hQmax i) (fun h => hf₁Q i (h hf₁D))).pow_left)
    have h1 : (1 : A) ∈ (P₀ * ∏ i, Q i ^ M) ⊔ D := by
      rw [Ideal.isCoprime_iff_sup_eq.1 hcop]; trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
    have hqd : (Algebra.norm k[X] f₁).natDegree + (q ^ M).natDegree ≤ d + 1 := by
      rw [hqm.natDegree_pow, hqdeg, hf₁deg, hd, hs]; nlinarith
    obtain ⟨p', hp'd, hp'⟩ := _root_.GlobalTheory.exists_lowDegree_coords_mod k A n b f₁ (q ^ M) d hf₁0 (pow_ne_zero _ hqm.ne_zero)
      hqd (u * y)
    rw [hspan M] at hp'
    have hP0 : P₀ * D * ∏ i, Q i ^ M ≤ D := Ideal.mul_le_left.trans Ideal.mul_le_right
    have hPI : P₀ * D * ∏ i, Q i ^ M ≤ P₀ * ∏ i, Q i ^ M := Ideal.mul_mono_left Ideal.mul_le_left
    refine ⟨∑ i, p' i • b i, ⟨?_, fun i => ?_⟩, ?_⟩
    · have : ∑ i, p' i • b i = u * y - (u * y - ∑ i, p' i • b i) := by ring
      rw [this]; exact D.sub_mem (D.mul_mem_left _ hy) (hP0 hp')
    · rw [b.repr_sum_self]; exact hp'd i
    · have : u - ∑ i, p' i • b i = u * x + (u * y - ∑ i, p' i • b i) := by
        linear_combination (-u) * hxy
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (hPI hp')
  · intro f hf hf0
    rw [finrank_quotient_span_eq_natDegree_norm b hf0, finrank_quotient_span_eq_natDegree_norm b hf₀0,
      hf₀deg]
    have := hdeg1 d (fun i => b.repr f i) hf.2
    rwa [b.sum_repr] at this
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearSystemMaximalDegreeFactorization =====
