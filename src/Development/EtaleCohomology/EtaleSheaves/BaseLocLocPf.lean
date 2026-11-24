module

public import Development.EtaleCohomology.EtaleSheaves.AlgebraicIntegralClosure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace LateralTheory.E.BaseLocLocPf

theorem pb_cancel {C : Type*} [Category C] {P X Y Z T : C} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {i : Z ⟶ T} [Mono i] (h : IsPullback a b (f ≫ i) (g ≫ i)) : IsPullback a b f g := by
  refine ⟨⟨by simpa [← cancel_mono i] using h.w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift s.fst s.snd (by simp [s.condition_assoc])) (fun s => by simp) (fun s => by simp) ?_⟩⟩
  intro s m h1 h2
  apply h.hom_ext <;> simp [h1, h2]

theorem loc_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (M : Submonoid A)
    (hf : @IsLocalization _ _ M _ _ f.toAlgebra) [Algebra B C] (N : Submonoid B) [IsLocalization N C] :
    ∃ M' : Submonoid A, @IsLocalization _ _ M' _ _ ((algebraMap B C).comp f).toAlgebra := by
  letI := f.toAlgebra
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨_, IsLocalization.localization_localization_isLocalization M N C⟩

theorem loc_equiv' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (e : B ≃+* C) :
    @IsLocalization _ _ M _ _ ((e : B →+* C).comp (algebraMap A B)).toAlgebra := by
  letI : Algebra A C := ((e : B →+* C).comp (algebraMap A B)).toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv M (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))

theorem chart {Z S : Scheme.{0}} (c : Z ⟶ S) (x : S) (W : (pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
    (y : (pullback c (S.fromSpecStalk x) : Scheme.{0})) (hy : y ∈ W) :
    ∃ U : (pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    ∃ V : Z.Opens, IsAffineOpen V ∧ (V : Set Z).Nonempty ∧
    ∃ f : Γ(Z, V) →+* Γ((pullback c (S.fromSpecStalk x) : Scheme.{0}), U), ∃ M : Submonoid Γ(Z, V),
      @IsLocalization _ _ M _ _ f.toAlgebra := by
  obtain ⟨U0, hU0a, hxU0, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : S.Opens) from trivial)
  have hg : S.fromSpecStalk x = Spec.map (S.presheaf.germ U0 x hxU0) ≫ hU0a.fromSpec :=
    (hU0a.fromSpecStalk_eq_fromSpecStalk hxU0).symm
  have hgU : ∀ z, S.fromSpecStalk x z ∈ U0 := by
    intro z; rw [hg, Scheme.Hom.comp_apply]; exact hU0a.range_fromSpec.le (Set.mem_range_self _)
  have hcy : c (pullback.fst c (S.fromSpecStalk x) y) ∈ U0 := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]; exact hgU _
  obtain ⟨V, hVa, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show pullback.fst c (S.fromSpecStalk x) y ∈ c ⁻¹ᵁ U0 from hcy)
  have hVU' : V ≤ c ⁻¹ᵁ U0 := hVU
  set p := pullback.fst c (S.fromSpecStalk x)
  set O := p ⁻¹ᵁ V with hOdef
  have H1 : IsPullback (p ∣_ V) O.ι V.ι p := isPullback_morphismRestrict p V
  have H2 : IsPullback (p ∣_ V) (O.ι ≫ pullback.snd c (S.fromSpecStalk x)) (V.ι ≫ c) (S.fromSpecStalk x) :=
    H1.paste_vert (IsPullback.of_hasPullback c (S.fromSpecStalk x))
  let ψ := c.appLE U0 V hVU'
  have e1 : V.ι ≫ c = hVa.isoSpec.hom ≫ Spec.map ψ ≫ hU0a.fromSpec := by
    rw [IsAffineOpen.SpecMap_appLE_fromSpec c hU0a hVa hVU', ← IsAffineOpen.isoSpec_inv_ι]; simp
  have H3 : IsPullback ((p ∣_ V) ≫ hVa.isoSpec.hom) (O.ι ≫ pullback.snd c (S.fromSpecStalk x)) (Spec.map ψ ≫ hU0a.fromSpec)
      (Spec.map (S.presheaf.germ U0 x hxU0) ≫ hU0a.fromSpec) := by
    rw [← hg]
    exact IsPullback.of_iso H2 (Iso.refl _) hVa.isoSpec (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [e1]) (by simp)
  have H4 := pb_cancel H3
  letI : Algebra Γ(S, U0) Γ(Z, V) := ψ.hom.toAlgebra
  letI := S.presheaf.algebra_section_stalk ⟨x, hxU0⟩
  haveI hSt : IsLocalization.AtPrime (S.presheaf.stalk x) (hU0a.primeIdealOf ⟨x, hxU0⟩).asIdeal :=
    hU0a.isLocalization_stalk ⟨x, hxU0⟩
  have H5 := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(S, U0) Γ(Z, V) (S.presheaf.stalk x))
  let e := H4.isoIsPullback _ _ H5
  haveI : IsAffine O.toScheme := IsAffine.of_isIso e.hom
  have hOa : IsAffineOpen O := this
  let eR : CommRingCat.of (Γ(Z, V) ⊗[Γ(S, U0)] S.presheaf.stalk x) ≅ Γ(pullback c (S.fromSpecStalk x), O) :=
    (Scheme.ΓSpecIso _).symm ≪≫ Scheme.Γ.mapIso e.op ≪≫ O.topIso
  have hL := loc_equiv' (Algebra.algebraMapSubmonoid Γ(Z, V) (hU0a.primeIdealOf ⟨x, hxU0⟩).asIdeal.primeCompl)
    eR.commRingCatIsoToRingEquiv
  have hyO : y ∈ O := hyV
  obtain ⟨h, hhW, hyh⟩ := hOa.exists_basicOpen_le (V := W) ⟨y, hy⟩ hyO
  haveI := hOa.isLocalization_basicOpen h
  obtain ⟨M, hM⟩ := loc_comp (C := Γ(pullback c (S.fromSpecStalk x), (pullback c (S.fromSpecStalk x)).basicOpen h)) _ _ hL (Submonoid.powers h)
  exact ⟨_, hyh, hhW, V, hVa, ⟨_, hyV⟩, _, M, hM⟩

theorem BaseLocLoc_of : LateralTheory.E.BaseAICPf.BaseLocLoc := by
  intro Z S c _ _ _ _ _ x W y hy
  exact chart c x W y hy

end LateralTheory.E.BaseLocLocPf
