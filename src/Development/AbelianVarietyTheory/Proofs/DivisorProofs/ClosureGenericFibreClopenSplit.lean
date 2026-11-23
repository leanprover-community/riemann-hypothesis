module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentTmulOneEqOfSmoothAlgebraStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComapIncludeRightFieldStatement
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
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem GlobalTheory.closure_generic_fibre_clopen_split : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ C C' : Set (PrimeSpectrum A), C ∪ C' = {r | r.asIdeal.comap (algebraMap R A) = ⊥} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  intro R A _ _ _ _ _ hsm C C' hU hd1 hd2
  let K := FractionRing R
  let f : A →+* A ⊗[R] K := (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] K).toRingHom
  let φ := PrimeSpectrum.comap f
  have hφc : Continuous φ := PrimeSpectrum.continuous_comap f

  have hF : {r : PrimeSpectrum A | r.asIdeal.comap (algebraMap R A) = ⊥} = Set.range φ := by
    have h1 := GlobalTheory.T.range_comap_includeRight_eq_comap_eq_ker R A K
    have hker : RingHom.ker (algebraMap R K) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
    rw [hker] at h1
    rw [← h1]
    let e := (Algebra.TensorProduct.comm R A K).toRingEquiv
    have hg : (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom = e.toRingHom.comp f := by
      ext a
      simp [f, e]
    rw [hg, PrimeSpectrum.comap_comp, Set.range_comp]
    have hsurj : Set.range (PrimeSpectrum.comap e.toRingHom) = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ⟨PrimeSpectrum.comap e.symm.toRingHom y, ?_⟩
      rw [← PrimeSpectrum.comap_comp_apply, RingEquiv.symm_toRingHom_comp_toRingHom]
      rfl
    rw [hsurj, Set.image_univ]

  have hinj : Function.Injective f := by
    have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R K)
      (IsFractionRing.injective R K)
    intro x y hxy
    have : (LinearMap.lTensor A (Algebra.linearMap R K)) ((TensorProduct.rid R A).symm x) =
        (LinearMap.lTensor A (Algebra.linearMap R K)) ((TensorProduct.rid R A).symm y) := by
      simpa [f] using hxy
    exact (TensorProduct.rid R A).symm.injective (hl this)
  have hdense : DenseRange φ :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2
      (by rw [(RingHom.injective_iff_ker_eq_bot f).1 hinj]; exact bot_le)
  have hCC' : Disjoint C C' := hd1.mono_right subset_closure
  have hunion : φ ⁻¹' C ∪ φ ⁻¹' C' = Set.univ := by
    rw [← Set.preimage_union, hU, hF, Set.preimage_range]
  have hcompl : IsCompl (φ ⁻¹' C) (φ ⁻¹' C') :=
    ⟨hCC'.preimage φ, codisjoint_iff.2 hunion⟩
  have hS1 : φ ⁻¹' closure C = φ ⁻¹' C := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.preimage_mono subset_closure)
    have hx' : x ∈ φ ⁻¹' C ∪ φ ⁻¹' C' := hunion ▸ Set.mem_univ x
    rcases hx' with h | h
    · exact h
    · exact absurd h (Set.disjoint_left.1 hd2 hx)
  have hclosed : IsClosed (φ ⁻¹' C) := hS1 ▸ isClosed_closure.preimage hφc
  have hS2 : φ ⁻¹' closure C' = φ ⁻¹' C' := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.preimage_mono subset_closure)
    have hx' : x ∈ φ ⁻¹' C ∪ φ ⁻¹' C' := hunion ▸ Set.mem_univ x
    rcases hx' with h | h
    · exact absurd hx (Set.disjoint_left.1 hd1 h)
    · exact h
  have hclosed' : IsClosed (φ ⁻¹' C') := hS2 ▸ isClosed_closure.preimage hφc
  have hopen : IsOpen (φ ⁻¹' C) := by
    rw [← isClosed_compl_iff, hcompl.compl_eq]; exact hclosed'
  obtain ⟨ε, hε, hεS⟩ := PrimeSpectrum.isClopen_iff.1 ⟨hclosed, hopen⟩
  obtain ⟨a, ha, haε⟩ := GlobalTheory.T.exists_idempotent_tmul_one_eq_of_smooth_algebra R A hsm ε hε
  have hfa : f a = ε := by simp [f, haε]
  have hpre : φ ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) = φ ⁻¹' C := by
    rw [hεS, ← hfa]
    ext x
    simp [φ, PrimeSpectrum.mem_basicOpen]
  have hCa : C ⊆ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
    intro x hx
    have hxF : x ∈ Set.range φ := hF ▸ hU ▸ Or.inl hx
    obtain ⟨y, rfl⟩ := hxF
    have hy : y ∈ φ ⁻¹' C := hx
    rw [← hpre] at hy
    exact hy
  have hC'a : C' ⊆ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A))ᶜ := by
    intro x hx
    have hxF : x ∈ Set.range φ := hF ▸ hU ▸ Or.inr hx
    obtain ⟨y, rfl⟩ := hxF
    have hy : y ∈ (φ ⁻¹' C)ᶜ := hcompl.compl_eq ▸ hx
    rw [← hpre] at hy
    exact hy
  have hclo : IsClopen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨a, ha, rfl⟩
  refine ⟨?_, ?_⟩
  · exact (disjoint_compl_right (a := (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)))).mono
      (closure_minimal hCa hclo.isClosed) (closure_minimal hC'a hclo.isOpen.isClosed_compl)
  · rw [← closure_union, hU, hF]
    exact hdense.closure_range
