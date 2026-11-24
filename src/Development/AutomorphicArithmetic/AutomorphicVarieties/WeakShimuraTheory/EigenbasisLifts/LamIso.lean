module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem pushCh_comp_alg {H O A B C : Type} [Group H] [CommRing O] [CommRing A] [CommRing B] [CommRing C]
    [Algebra O A] [Algebra O B] [Algebra O C] (f : A →ₐ[O] B) (g : B →ₐ[O] C) (χ : H →* Aˣ) :
    W.pushCh ((g.comp f : A →ₐ[O] C) : A →+* C) χ = W.pushCh (g : B →+* C) (W.pushCh (f : A →+* B) χ) := by
  ext s
  rfl

private theorem pushCh_id_alg {H O A : Type} [Group H] [CommRing O] [CommRing A] [Algebra O A] (χ : H →* Aˣ) :
    W.pushCh ((AlgHom.id O A : A →ₐ[O] A) : A →+* A) χ = χ := by
  ext s
  rfl

theorem UpperTheory.V.Ws.Eb.lamIso :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (Λ Λ' : W.LamObj r), Nonempty (Λ.Λ ≃ₐ[O] Λ'.Λ) := by
  intro l _ F O _ _ _ n r Λ Λ'
  obtain ⟨f, hf, -⟩ := Λ.univ Λ'.Λ Λ'.κ Λ'.inert
  obtain ⟨g, hg, -⟩ := Λ'.univ Λ.Λ Λ.κ Λ.inert
  refine ⟨AlgEquiv.ofAlgHom f g ?_ ?_⟩
  · exact (Λ'.univ Λ'.Λ Λ'.κ Λ'.inert).unique
      (fun v i => by rw [pushCh_comp_alg, hg, hf]) (fun v i => pushCh_id_alg _)
  · exact (Λ.univ Λ.Λ Λ.κ Λ.inert).unique
      (fun v i => by rw [pushCh_comp_alg, hf, hg]) (fun v i => pushCh_id_alg _)
