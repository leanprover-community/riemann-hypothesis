module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem appLE_comp_cst {R : Type} [CommRing R] {W W' : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (π : W' ⟶ W) (U : W.Opens) (A : W'.Opens) (h : A ≤ π ⁻¹ᵁ U) :
    (π.appLE U A h).hom.comp (cst f U) = cst (π ≫ f) A := by
  have e : f.appTop ≫ W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ π.appLE U A h =
      (π ≫ f).appTop ≫ W'.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop]
    simp [Scheme.Hom.appLE]
  ext r
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

theorem cst_comp_specMap {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {W : Scheme.{0}}
    (p : W ⟶ Spec (CommRingCat.of C)) (U : W.Opens) :
    cst (p ≫ Spec.map (CommRingCat.ofHom φ)) U = (cst p U).comp φ := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem comap_baseIdeal {R : Type} [CommRing R] {W W' : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (π : W' ⟶ W) (J : Ideal R) : (baseIdeal f J).comap π = baseIdeal (π ≫ f) J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {p : W.affineOpens × W'.affineOpens // p.2.1 ≤ π ⁻¹ᵁ p.1.1}) (fun i => i.1.2) ?_ ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
      ((iSup_affineOpens_eq_top W).ge (Set.mem_univ (π x)))
    obtain ⟨A, hA, hxA, hAU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 W'.isBasis_affineOpens (show x ∈ π ⁻¹ᵁ U.1 from hxU)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(U, ⟨A, hA⟩), hAU⟩, hxA⟩
  · intro i
    rw [GlobalTheory.Principalise.comapIdealAffine _ π i.1.1 i.1.2 i.2, baseIdeal_ideal, baseIdeal_ideal, Ideal.map_map,
      appLE_comp_cst]

theorem baseIdeal_comp_specMap {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {W : Scheme.{0}}
    (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R) :
    baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ) := by
  rw [baseIdeal, baseIdeal, Ideal.map_map, cst_comp_specMap]

theorem mem_support_baseIdeal {R : Type} [CommRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (J : Ideal R) (x : W) : x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal := by
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
    ((iSup_affineOpens_eq_top W).ge (Set.mem_univ x))
  have key : ∀ r, x ∈ W.basicOpen (cst f U.1 r) ↔ r ∉ (f x).asIdeal := by
    intro r
    simp only [cst, rs, RingHom.comp_apply]
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    simp only [hxU, TopologicalSpace.Opens.mem_inf, true_and]
    exact PrimeSpectrum.mem_basicOpen _ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, baseIdeal_ideal]
  unfold Ideal.map
  rw [Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h r hr
    by_contra hn
    exact h _ ⟨r, hr, rfl⟩ ((key r).2 hn)
  · rintro h _ ⟨r, hr, rfl⟩ hx
    exact (key r).1 hx (h hr)

theorem baseIdeal_calculus :
    (∀ (R : Type) [CommRing R] (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (J : Ideal R), (baseIdeal f J).comap π = baseIdeal (π ≫ f) J) ∧ (∀ (R C : Type) [CommRing R] [CommRing C] (φ : R →+* C) (W : Scheme.{0}) (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R), baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ)) ∧ (∀ (R : Type) [CommRing R] (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (x : W), x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal) :=
  ⟨fun _ _ _ _ f π J => comap_baseIdeal f π J,
    fun _ _ _ _ φ _ p J => baseIdeal_comp_specMap φ p J,
    fun _ _ _ f J x => mem_support_baseIdeal f J x⟩

end GlobalTheory.FormalAlg
