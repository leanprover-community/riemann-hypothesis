module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapCompAlgebraMap
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafExcisionShortExactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactMappingConeResolutionHomotopyEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.Refinements
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ExcisionQis

theorem map_descShortComplex {C : Type*} [Category C] [Abelian C] {K₁ K₂ L₁ L₂ M : CochainComplex C ℤ}
    (f' : K₁ ⟶ K₂) (g' : K₂ ⟶ M) (w' : f' ≫ g' = 0) (f : L₁ ⟶ L₂) (g : L₂ ⟶ M) (w : f ≫ g = 0)
    (a : K₁ ⟶ L₁) (b : K₂ ⟶ L₂) (comm : f' ≫ b = a ≫ f) (hg : g' = b ≫ g) :
    mappingCone.map f' f a b comm ≫ mappingCone.descShortComplex (ShortComplex.mk f g w) =
      mappingCone.descShortComplex (ShortComplex.mk f' g' w') := by
  ext n : 1
  apply mappingCone.ext_from _ (n + 1) n rfl
  · simp [mappingCone.map, mappingCone.descShortComplex, HomComplex.Cochain.zero_cochain_comp_v]
  · simp [mappingCone.map, mappingCone.descShortComplex, hg]

theorem cone_single_qis {C : Type*} [Category C] [Abelian C] {F1 F2 F3 F4 : C} (u' : F1 ⟶ F2) (u : F3 ⟶ F4)
    (a : F1 ⟶ F3) (b : F2 ⟶ F4) (comm : u' ≫ b = a ≫ u) [Mono u] (w : biprod.lift a (-u') ≫ biprod.desc u b = 0)
    (hS : (ShortComplex.mk _ _ w).ShortExact) :
    QuasiIso (mappingCone.map ((singleFunctor C 0).map u') ((singleFunctor C 0).map u) ((singleFunctor C 0).map a)
      ((singleFunctor C 0).map b) (by rw [← Functor.map_comp, ← Functor.map_comp, comm])) := by
  haveI : Mono (biprod.lift a (-u')) := hS.mono_f
  haveI : Epi (biprod.desc u b) := hS.epi_g
  let T : ShortComplex C := ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel u))
    inferInstance inferInstance
  have w' : u' ≫ b ≫ cokernel.π u = 0 := by
    rw [← Category.assoc, comm, Category.assoc, cokernel.condition, Limits.comp_zero]
  let T' : ShortComplex C := ShortComplex.mk u' (b ≫ cokernel.π u) w'
  have hmono : Mono u' := by
    refine Preadditive.mono_of_cancel_zero _ fun {Q} g hg => ?_
    have hga : g ≫ a = 0 := by
      rw [← cancel_mono u, Category.assoc, ← comm, ← Category.assoc, hg, Limits.zero_comp, Limits.zero_comp]
    have : g ≫ biprod.lift a (-u') = 0 := by
      apply biprod.hom_ext <;> simp [hga, hg]
    rw [← cancel_mono (biprod.lift a (-u')), this, Limits.zero_comp]
  have hepi : Epi (b ≫ cokernel.π u) := by
    refine Preadditive.epi_of_cancel_zero _ fun {Q} h hh => ?_
    have h1 : biprod.desc u b ≫ cokernel.π u ≫ h = 0 := by
      apply biprod.hom_ext'
      · simp
      · simpa using hh
    have h2 : cokernel.π u ≫ h = 0 := by
      rw [← cancel_epi (biprod.desc u b), h1, Limits.comp_zero]
    rw [← cancel_epi (cokernel.π u), h2, Limits.comp_zero]
  have hexact : T'.Exact := by
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A₀ y hy
    have hy' : (y ≫ b) ≫ T.g = 0 := by simpa using hy
    obtain ⟨A₁, e₁, he₁, z, hz⟩ := (ShortComplex.exact_iff_exact_up_to_refinements T).1 hT.exact (y ≫ b) hy'
    have hw : biprod.lift (-z) (e₁ ≫ y) ≫ (ShortComplex.mk _ _ w).g = 0 := by
      change biprod.lift (-z) (e₁ ≫ y) ≫ biprod.desc u b = 0
      rw [biprod.lift_desc, Preadditive.neg_comp, Category.assoc, hz]
      exact neg_add_cancel _
    obtain ⟨A₂, e₂, he₂, x, hx⟩ := (ShortComplex.exact_iff_exact_up_to_refinements _).1 hS.exact _ hw
    refine ⟨A₂, e₂ ≫ e₁, inferInstance, -x, ?_⟩
    have h2 := congrArg (· ≫ biprod.snd) hx
    simp only [Category.assoc] at h2
    rw [biprod.lift_snd, biprod.lift_snd] at h2
    show (e₂ ≫ e₁) ≫ y = (-x) ≫ u'
    rw [Category.assoc, h2, Preadditive.neg_comp, Preadditive.comp_neg]
  have hT' : T'.ShortExact := ShortComplex.ShortExact.mk' hexact hmono hepi
  have z1 : (singleFunctor C 0).map u ≫ (singleFunctor C 0).map (cokernel.π u) = 0 := by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have z2 : (singleFunctor C 0).map u' ≫ (singleFunctor C 0).map (b ≫ cokernel.π u) = 0 := by
    rw [← Functor.map_comp, w', Functor.map_zero]
  have c2 : (singleFunctor C 0).map u' ≫ (singleFunctor C 0).map b = (singleFunctor C 0).map a ≫ (singleFunctor C 0).map u := by
    rw [← Functor.map_comp, ← Functor.map_comp, comm]
  have hST : (ShortComplex.mk _ _ z1).ShortExact := hT.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)
  have hST' : (ShortComplex.mk _ _ z2).ShortExact := hT'.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)
  haveI := mappingCone.quasiIso_descShortComplex hST
  haveI := mappingCone.quasiIso_descShortComplex hST'
  have key := map_descShortComplex _ _ z2 _ _ z1 ((singleFunctor C 0).map a) ((singleFunctor C 0).map b) c2
    (Functor.map_comp _ _ _)
  haveI : QuasiIso (mappingCone.map _ _ _ _ c2 ≫ mappingCone.descShortComplex (ShortComplex.mk _ _ z1)) := by
    rw [key]; exact mappingCone.quasiIso_descShortComplex hST'
  exact quasiIso_of_comp_right _ (mappingCone.descShortComplex (ShortComplex.mk _ _ z1))

theorem mono_free_away (R : Type) [CommRing R] (A : Type) [CommRing A] (f : A) :
    Mono ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) := by
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) :=
    IsOpenImmersion.of_isLocalization f
  have h1 : Mono (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))) := inferInstance
  have h2 : Mono ((freeP R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) := by
    have happ : ∀ U, Mono (((freeP R).map (yoneda.map (Spec.map (CommRingCat.ofHom
        (algebraMap A (Localization.Away f)))))).app U) := fun U => by
      have hinj : Function.Injective
          ((yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))).app U) :=
        (mono_iff_injective _).1 inferInstance
      rw [ModuleCat.mono_iff_injective]
      change Function.Injective (Finsupp.mapDomain _)
      exact Finsupp.mapDomain_injective (fun x y hxy => ULift.ext (hinj (congrArg ULift.down hxy)))
    exact NatTrans.mono_of_mono_app _
  change Mono ((presheafToSheaf _ _).map ((freeP R).map _))
  infer_instance

theorem quasiIso_map_of_corners {C : Type*} [Category C] [Abelian C] {K₁ K₂ K₃ K₄ L₁ L₂ L₃ L₄ : CochainComplex C ℤ}
    (φ' : K₁ ⟶ K₂) (φ : K₃ ⟶ K₄) (α : K₁ ⟶ K₃) (β : K₂ ⟶ K₄) (c₀ : φ' ≫ β = α ≫ φ)
    (ψ' : L₁ ⟶ L₂) (ψ : L₃ ⟶ L₄) (α' : L₁ ⟶ L₃) (β' : L₂ ⟶ L₄) (c₁ : ψ' ≫ β' = α' ≫ ψ)
    (e₁ : K₁ ⟶ L₁) (e₂ : K₂ ⟶ L₂) (e₃ : K₃ ⟶ L₃) (e₄ : K₄ ⟶ L₄) (q₁ : QuasiIso e₁) (q₂ : QuasiIso e₂)
    (q₃ : QuasiIso e₃) (q₄ : QuasiIso e₄) (h₁₂ : φ' ≫ e₂ = e₁ ≫ ψ') (h₃₄ : φ ≫ e₄ = e₃ ≫ ψ) (h₁₃ : α ≫ e₃ = e₁ ≫ α')
    (h₂₄ : β ≫ e₄ = e₂ ≫ β') [QuasiIso (mappingCone.map φ' φ α β c₀)] :
    QuasiIso (mappingCone.map ψ' ψ α' β' c₁) := by
  haveI := q₁; haveI := q₂; haveI := q₃; haveI := q₄
  have key : mappingCone.map φ' ψ' e₁ e₂ h₁₂ ≫ mappingCone.map ψ' ψ α' β' c₁ =
      mappingCone.map φ' φ α β c₀ ≫ mappingCone.map φ ψ e₃ e₄ h₃₄ := by
    rw [← mappingCone.map_comp, ← mappingCone.map_comp]
    congr 1
    · exact h₁₃.symm
    · exact h₂₄.symm
  haveI := GlobalTheory.EtC.ConeRes.quasiIso_mappingCone_map φ' ψ' e₁ e₂ h₁₂
  haveI := GlobalTheory.EtC.ConeRes.quasiIso_mappingCone_map φ ψ e₃ e₄ h₃₄
  haveI : QuasiIso (mappingCone.map φ' ψ' e₁ e₂ h₁₂ ≫ mappingCone.map ψ' ψ α' β' c₁) := by
    rw [key]; infer_instance
  exact quasiIso_of_comp_left (mappingCone.map φ' ψ' e₁ e₂ h₁₂) _

private theorem biprod_lift_neg_desc_eq_zero {C : Type*} [Category C] [Abelian C]
    {X₁ X₂ X₃ X₄ : C} {u' : X₁ ⟶ X₂} {u : X₃ ⟶ X₄} {a : X₁ ⟶ X₃} {b : X₂ ⟶ X₄}
    (comm : u' ≫ b = a ≫ u) : biprod.lift a (-u') ≫ biprod.desc u b = 0 := by
  rw [biprod.lift_desc, Preadditive.neg_comp, ← comm, add_neg_cancel]

private theorem cone_qis_of_natural_homotopyEquiv {P C : Type*} [Category P] [Category C] [Abelian C]
    (F : P ⥤ C) (G : P ⥤ CochainComplex C ℤ) {X₁ X₂ X₃ X₄ : P}
    (u' : X₁ ⟶ X₂) (u : X₃ ⟶ X₄) (a : X₁ ⟶ X₃) (b : X₂ ⟶ X₄)
    (sq : CommSq u' a b u) [Mono (F.map u)]
    (hS : ∀ w : biprod.lift (F.map a) (-F.map u') ≫ biprod.desc (F.map u) (F.map b) = 0,
      (ShortComplex.mk _ _ w).ShortExact)
    (e : ∀ X, HomotopyEquiv ((singleFunctor C 0).obj (F.obj X)) (G.obj X))
    (he : ∀ {X Y : P} (g : X ⟶ Y),
      (e X).hom ≫ G.map g = (singleFunctor C 0).map (F.map g) ≫ (e Y).hom) :
    QuasiIso (mappingCone.map (G.map u') (G.map u) (G.map a) (G.map b) (G.map_commSq sq).w) := by
  let S := F ⋙ singleFunctor C 0
  have commS := (S.map_commSq sq).w
  have commF := (F.map_commSq sq).w
  have w := biprod_lift_neg_desc_eq_zero commF
  have : QuasiIso (mappingCone.map (S.map u') (S.map u) (S.map a) (S.map b) commS) :=
    cone_single_qis (F.map u') (F.map u) (F.map a) (F.map b) commF w (hS w)
  exact quasiIso_map_of_corners (S.map u') (S.map u) (S.map a) (S.map b) commS
    (G.map u') (G.map u) (G.map a) (G.map b) (G.map_commSq sq).w
    (e X₁).hom (e X₂).hom (e X₃).hom (e X₄).hom
    (e X₁).quasiIso_hom (e X₂).quasiIso_hom (e X₃).quasiIso_hom (e X₄).quasiIso_hom
    (he u').symm (he u).symm (he a).symm (he b).symm

theorem _root_.GlobalTheory.EtC.excisionConeMap_quasiIso : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A), IsExcisionNbhd A A' f → QuasiIso (excisionConeMap R A A' f) := by
  intro R _ A A' _ _ _ f h
  obtain ⟨e, -, he⟩ := chains_disc_homotopyEquiv R
  have : Algebra.Etale A A' := h.1
  let u' := (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))).op
  let u := (CommRingCat.ofHom (algebraMap A (Localization.Away f))).op
  let a := (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)).op
  let b := (CommRingCat.ofHom (algebraMap A A')).op
  have sq : CommSq u' a b u := ⟨
    congrArg (fun g => (CommRingCat.ofHom g).op) (awayMap_comp_algebraMap (algebraMap A A') f).symm⟩
  let Y : CommRingCat.{0}ᵒᵖ ⥤ PSh := Scheme.Spec ⋙ yoneda
  let F := Y ⋙ free R
  have hS := GlobalTheory.T.freeEtaleSheaf_excision_shortExact R A A' f ⟨h.2.1, h.2.2⟩
  have : Mono (F.map u) := mono_free_away R A f
  exact cone_qis_of_natural_homotopyEquiv F (Y ⋙ disc ⋙ chains R) u' u a b sq
    hS (fun X => e (Y.obj X)) (fun g => he (Y.map g))

end GlobalTheory.EtC.ExcisionQis

end
