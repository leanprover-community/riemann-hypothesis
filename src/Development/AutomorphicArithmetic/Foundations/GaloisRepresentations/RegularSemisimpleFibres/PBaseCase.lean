module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.BaseCase
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def selfPl {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : PlacesOver K v :=
  ⟨v, ⟨Ideal.ext fun _ => Iff.rfl⟩⟩

private theorem cm_id {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : completionMap v (selfPl v).1 x = x := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    (continuous_completionMap v (selfPl v).1) continuous_id (funext fun y => ?_)) x
  simp only [Function.comp_apply, id]
  rw [completionMap_algebraMap]
  rfl

private theorem map_refl {R : Type} [CommRing R] {n : ℕ} (g : GL (Fin n) R) :
    Matrix.GeneralLinearGroup.map (RingEquiv.refl R).toRingHom g = g := by
  ext i j
  simp

theorem UpperTheory.Gal.InertialTypesAlt.baseCase :
    ResEmbCompat → LblIso → BaseCase := by
  intro hC hI K Ω _ _ _ _ _ n π A Θ v e e' he he' τ τ' hτ hτ' a ha
  have H : ∃ (r : 𝓀[v.adicCompletion K] →+* 𝓀[v.adicCompletion K])
      (j : AlgebraicClosure 𝓀[v.adicCompletion K] ≃+* AlgebraicClosure 𝓀[v.adicCompletion K]),
      (∀ (x y : 𝒪[v.adicCompletion K]), (y : v.adicCompletion K) = x →
        IsLocalRing.residue _ y = r (IsLocalRing.residue _ x)) ∧
      (∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) ∧ ∀ x, e' (j x) = e x := by
    obtain ⟨r, j, h1, h2, h3⟩ := hC K K Ω A v (selfPl v) e e' he he'
    exact ⟨r, j, fun x y h => h1 x y (h.trans (cm_id v _).symm), h2, h3⟩
  obtain ⟨r, j, h1, h2, h3⟩ := H
  obtain ⟨E⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π v τ τ' hτ hτ'
  have hθ : (Θ.comp e'.toMonoidHom).comp j.toMonoidHom = Θ.comp e.toMonoidHom := by
    ext x
    simp [h3]
  refine hI (v.adicCompletion K) (v.adicCompletion K) (RingEquiv.refl _) (fun _ => Iff.rfl) j ?_
    (Θ.comp e'.toMonoidHom) n τ.V τ'.V τ.ρ τ'.ρ E.toLinearEquiv ?_ a (by rw [hθ]; exact ha)
  · intro x y hxy
    rw [h2, h1 x y hxy]
  · intro g x
    rw [map_refl]
    exact LinearMap.congr_fun (E.isIntertwining' g) x
