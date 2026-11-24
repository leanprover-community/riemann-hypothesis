module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleQuasiSectionOfSmoothSchemeHomStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem smooth_surjective_loc_sections : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f] (U : Scheme.{0}) (y : U ⟶ X), Loc U fun V g => ∃ x : V ⟶ Y, x ≫ f = g ≫ y := by
  intro Y X f _ _ U y
  refine (loc_iff_etale_affine_points U (fun V g => ∃ x : V ⟶ Y, x ≫ f = g ≫ y) ?_).2 ?_
  · rintro V W g k ⟨x, hx⟩
    exact ⟨k ≫ x, by simp [Category.assoc, hx]⟩
  · intro u
    obtain ⟨V, s, hE, hu⟩ := GlobalTheory.T.exists_etale_quasiSection_of_smooth_scheme_hom f (y u) (f.surjective (y u))
    obtain ⟨v, hv⟩ := hu
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback v u hv
    let W := pullback (s ≫ f) y
    obtain ⟨z, hz⟩ := W.affineCover.covers w
    haveI := hE
    have hEt : Etale (pullback.snd (s ≫ f) y) := inferInstance
    refine ⟨_, W.affineCover.f (W.affineCover.idx w) ≫ pullback.snd (s ≫ f) y, inferInstance, inferInstance, ⟨z, ?_⟩, ?_⟩
    · simp [hz, hw2]
    · refine ⟨W.affineCover.f (W.affineCover.idx w) ≫ pullback.fst (s ≫ f) y ≫ s, ?_⟩
      simp only [Category.assoc]
      rw [show pullback.fst (s ≫ f) y ≫ s ≫ f = pullback.snd (s ≫ f) y ≫ y from pullback.condition]

end GlobalTheory.EtC
