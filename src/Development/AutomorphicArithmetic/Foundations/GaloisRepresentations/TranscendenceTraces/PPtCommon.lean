module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
public import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.ptCommon_of :
    PtCommon := by
  intro X Ω Ω' _ _ z z' h
  have key : ∀ (K : Type) [Field K] (w : gp K ⟶ X) (y : X), pt w = y →
      ∃ ψ : X.residueField y ⟶ CommRingCat.of K, w = Spec.map ψ ≫ X.fromSpecResidueField y := by
    intro K _ w y hy
    subst hy
    exact ⟨_, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X w).symm⟩
  obtain ⟨x, hx⟩ : ∃ x, pt z = x := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ := key Ω z x hx
  obtain ⟨φ', hφ'⟩ := key Ω' z' x (h.symm.trans hx)
  have i1 : Function.Injective φ.hom := φ.hom.injective
  have i2 : Function.Injective φ'.hom := φ'.hom.injective
  letI := φ.hom.toAlgebra
  letI := φ'.hom.toAlgebra
  haveI : Nontrivial (TensorProduct (X.residueField x) Ω Ω') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ i1 i2
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct (X.residueField x) Ω Ω')
  letI := Ideal.Quotient.field M
  let ψ : TensorProduct (X.residueField x) Ω Ω' →+* AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M) :=
    (algebraMap _ _).comp (Ideal.Quotient.mk M)
  have e1 : ∀ c, (φ.hom c ⊗ₜ[X.residueField x] (1 : Ω') : TensorProduct (X.residueField x) Ω Ω') =
      (1 : Ω) ⊗ₜ (φ'.hom c) := by
    intro c
    change algebraMap _ Ω c ⊗ₜ _ = _ ⊗ₜ algebraMap _ Ω' c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  refine ⟨AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (ψ.comp Algebra.TensorProduct.includeLeftRingHom)),
    Spec.map (CommRingCat.ofHom (ψ.comp (Algebra.TensorProduct.includeRight :
      Ω' →ₐ[X.residueField x] TensorProduct (X.residueField x) Ω Ω').toRingHom)), ?_⟩
  rw [hφ, hφ', ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext c
  simp [e1]
