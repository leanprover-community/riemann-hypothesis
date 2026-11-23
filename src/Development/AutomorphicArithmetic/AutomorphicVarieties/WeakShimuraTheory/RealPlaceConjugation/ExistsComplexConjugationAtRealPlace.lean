module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.Hypotheses.GalCohDefs
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.exists_complexConjugation_at_realPlace :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : InfinitePlace F), w.IsReal → ∃ c : G F Ω, IsCCAt w c := by
  intro F Ω _ _ _ _ _ w hw
  let φ : F →+* ℂ := w.embedding
  have hreal : ∀ x : F, starRingEnd ℂ (φ x) = φ x := by
    intro x
    have h := congrArg (fun ψ : F →+* ℂ => ψ x)
      (NumberField.ComplexEmbedding.isReal_iff.mp (NumberField.InfinitePlace.isReal_iff.mp hw))
    simpa using h
  letI : Algebra F ℂ := φ.toAlgebra
  have halg : ∀ x : F, algebraMap F ℂ x = φ x := fun x => rfl
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  let j : Ω →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let E : IntermediateField F ℂ := j.fieldRange
  let e : Ω ≃ₐ[F] E := AlgEquiv.ofInjectiveField j
  haveI : Normal F E := Normal.of_algEquiv e
  let cj : ℂ →ₐ[F] ℂ :=
    { (starRingEnd ℂ : ℂ →+* ℂ) with
      commutes' := fun x => by
        show starRingEnd ℂ (algebraMap F ℂ x) = algebraMap F ℂ x
        rw [halg]; exact hreal x }
  have hrange : (cj.comp E.val).fieldRange = E := AlgHom.fieldRange_of_normal _
  have hmem : ∀ y : Ω, starRingEnd ℂ (j y) ∈ E := by
    intro y
    have h1 : (cj.comp E.val) (e y) ∈ (cj.comp E.val).fieldRange := AlgHom.mem_fieldRange.mpr ⟨e y, rfl⟩
    rw [hrange] at h1
    have h2 : ((e y : E) : ℂ) = j y := rfl
    simpa [cj, h2] using h1
  let f' : Ω →ₐ[F] E := (cj.comp j).codRestrict E.toSubalgebra (fun y => hmem y)
  let σ0 : Ω →ₐ[F] Ω := e.symm.toAlgHom.comp f'
  have hbij : Function.Bijective σ0 := Algebra.IsAlgebraic.algHom_bijective σ0
  let c : Ω ≃ₐ[F] Ω := AlgEquiv.ofBijective σ0 hbij
  refine ⟨c, (j : Ω →+* ℂ), ?_, ?_⟩
  · intro x
    have h3 : ((e (e.symm (f' x)) : E) : ℂ) = j (e.symm (f' x)) := rfl
    rw [AlgEquiv.apply_symm_apply] at h3
    show j (e.symm (f' x)) = starRingEnd ℂ (j x)
    rw [← h3]
    rfl
  · have h4 : (j : Ω →+* ℂ).comp (algebraMap F Ω) = φ := by
      ext x
      simp [halg]
    rw [h4]
    exact NumberField.InfinitePlace.mk_embedding w
