module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

@[expose] public section

open NumberField UpperTheory.V.Af.Bc

private theorem range_res_eq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Field K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] :
    (res F Ω K).range = (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨τ, rfl⟩ y hy
    obtain ⟨k, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact τ.commutes k
  · intro h
    refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) fun k => h _ (AlgHom.mem_fieldRange.mpr ⟨k, rfl⟩), ?_⟩
    ext y
    rfl

private theorem equiv_of_range {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω] (K K' : Type) [Field K] [Algebra F K]
    [Algebra K Ω] [IsScalarTower F K Ω] [Field K'] [Algebra F K'] [Algebra K' Ω] [IsScalarTower F K' Ω]
    (h : (res F Ω K).range = (res F Ω K').range) : Nonempty (K ≃ₐ[F] K') := by
  have hK := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K Ω).fieldRange
  have hK' := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K' Ω).fieldRange
  rw [range_res_eq, range_res_eq] at h
  have he : (IsScalarTower.toAlgHom F K Ω).fieldRange = (IsScalarTower.toAlgHom F K' Ω).fieldRange := by
    rw [← hK, ← hK', h]
  have he' : (IsScalarTower.toAlgHom F K Ω).range = (IsScalarTower.toAlgHom F K' Ω).range := by
    rw [← AlgHom.fieldRange_toSubalgebra, ← AlgHom.fieldRange_toSubalgebra, he]
  exact ⟨(AlgEquiv.ofInjectiveField _).trans
    ((Subalgebra.equivOfEq _ _ he').trans (AlgEquiv.ofInjectiveField _).symm)⟩

theorem UpperTheory.V.Br.signNe :
    UpperTheory.V.Br.SignNe := by
  intro K K' Ω _ _ _ _ _ _ _ _ _ _ _ hK hcop heq
  obtain ⟨e⟩ := equiv_of_range K K' heq
  rw [← NumberField.discr_eq_discr_of_algEquiv (K := K) e, isCoprime_self, Int.isUnit_iff] at hcop
  have := NumberField.abs_discr_gt_two (K := K) (by omega)
  rcases hcop with h | h <;> rw [h] at this <;> norm_num at this
