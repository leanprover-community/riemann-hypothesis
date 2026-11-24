module

public import Formalism.LocalRingCardinality.DataTheta
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.FockKFin

theorem sameBlock_iff_isLeft {p q : ℕ} (a b : Ix p q) : sameBlock a b ↔ a.isLeft = b.isLeft := by
  cases a <;> cases b <;> simp [sameBlock]

theorem isKC_one {p q : ℕ} : IsKC (1 : Mat p q) := by
  intro a b h
  apply Matrix.one_apply_ne
  rintro rfl
  exact h ((sameBlock_iff_isLeft a a).2 rfl)

theorem isKC_kronecker {p q r s : ℕ} (A : Mat p q) (B : Mat r s) (hA : IsKC A) (hB : IsKC B) :
    IsKC (Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      (Matrix.kroneckerMap (· * ·) A B)) := by
  intro x y hxy
  obtain ⟨⟨a, c⟩, rfl⟩ := (lineEquiv p q r s).surjective x
  obtain ⟨⟨b, d⟩, rfl⟩ := (lineEquiv p q r s).surjective y
  rw [sameBlock_iff_isLeft, lineEquiv_isLeft, lineEquiv_isLeft] at hxy
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply]
  by_cases h1 : sameBlock a b
  · by_cases h2 : sameBlock c d
    · exfalso
      apply hxy
      cases a <;> cases b <;> cases c <;> cases d <;> simp_all [sameBlock, linePos]
    · rw [hB c d h2, mul_zero]
  · rw [hA a b h1, zero_mul]

theorem emb_mem_Kset {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)}
    {T1 : GrpData p q} {T2 : GrpData r s} (F : FockData T0 T1 T2) {g : T1.G} {h : T2.G}
    (hg : g ∈ T1.Kset) (hh : h ∈ T2.Kset) : F.emb (g, h) ∈ T0.Kset := by
  change IsKC _
  rw [F.emb_cov]
  exact isKC_kronecker _ _ hg hh

theorem one_mem_Kset {p q : ℕ} (T : GrpData p q) : (1 : T.G) ∈ T.Kset := by
  change IsKC _
  rw [map_one, Units.val_one]
  exact isKC_one

theorem exists_finite {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)}
    {T1 : GrpData p q} {T2 : GrpData r s} (F : FockData T0 T1 T2)
    (H : ∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d,
      ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q) (P : Pol p q r s) :
    ∃ W : Submodule ℂ F.H, FiniteDimensional ℂ W ∧ ∀ k ∈ T0.Kset, F.Om k (F.ι P) ∈ W := by
  refine ⟨(MvPolynomial.restrictTotalDegree (Ix p q × Ix r s) ℂ P.totalDegree).map F.ι,
    inferInstance, fun k hk => ?_⟩
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent P]

  rw [map_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  obtain ⟨Q, hQ, e⟩ := H k hk d _ (MvPolynomial.homogeneousComponent_mem d P)
  rw [e]
  refine Submodule.mem_map_of_mem ?_
  rw [MvPolynomial.mem_restrictTotalDegree]
  have h1 : Q.totalDegree ≤ d := MvPolynomial.IsHomogeneous.totalDegree_le hQ
  have h2 := Finset.mem_range.1 hd
  omega

theorem kfin_fock : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), (∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d, ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q) → ∀ P : Pol p q r s, KFin T1 (fun g => F.π (g, 1)) (F.ι P) ∧ KFin T2 (fun h => F.π (1, h)) (F.ι P) := by
  intro p q r s T0 T1 T2 F H P
  obtain ⟨W, hW, hmem⟩ := exists_finite F H P
  constructor
  · refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hmem _ (emb_mem_Kset F k.2 (one_mem_Kset T2))
  · refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hmem _ (emb_mem_Kset F (one_mem_Kset T1) k.2)

end GlobalTheory.FockKFin
