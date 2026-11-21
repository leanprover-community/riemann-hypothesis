import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSurjectionCechDescentTateTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeraySimplicialCocycleCoboundaryOfAcyclicLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyFiniteKillingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentVanishingFiniteAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcycFOfPiSh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSepClosedResidueFieldOfModuleFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNervePullbackBijectiveDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenseliaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInductionStatement

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

noncomputable def cechDiagApp {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) :
    yoneda.obj Y ⟶ widePullback (yoneda.obj X) (fun _ : Fin (k + 1) => yoneda.obj Y) (fun _ => yoneda.map f) :=
  WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (by intro; exact Category.id_comp _)

@[reassoc (attr := simp)]
theorem cechDiagApp_π {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) (j : Fin (k + 1)) :
    cechDiagApp f k ≫ WidePullback.π _ j = 𝟙 _ := WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
theorem cechDiagApp_base {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) :
    cechDiagApp f k ≫ WidePullback.base _ = yoneda.map f := WidePullback.lift_base _ _ _ _

noncomputable def cechDiag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := cechDiagApp f n.unop.len
  naturality n m g := by
    change 𝟙 (yoneda.obj Y) ≫ cechDiagApp f m.unop.len = cechDiagApp f n.unop.len ≫ _
    rw [Category.id_comp]
    apply WidePullback.hom_ext
    · intro j
      rw [cechDiagApp_π]
      erw [Category.assoc, WidePullback.lift_π]
      exact (cechDiagApp_π f _ _).symm
    · rw [cechDiagApp_base]
      refine Eq.trans ?_ (Category.assoc (cechDiagApp f _) ((cech f).map g) _).symm
      erw [WidePullback.lift_base]
      exact (cechDiagApp_base f _).symm

theorem cechDiag_spec {Y X : Scheme.{0}} (f : Y ⟶ X) :
    ∃ Δ : sch.obj Y ⟶ cech f, IsIso (Δ.app (op ⦋0⦌)) ∧ Δ ≫ cechAug f = sch.map f := by
  refine ⟨cechDiag f, ?_, ?_⟩
  · refine ⟨⟨(WidePullback.π (fun _ : Fin (0 + 1) => yoneda.map f) 0 : _ ⟶ yoneda.obj Y), ?_, ?_⟩⟩
    · exact cechDiagApp_π f 0 0
    · change WidePullback.π (fun _ : Fin (0 + 1) => yoneda.map f) 0 ≫ cechDiagApp f 0 = 𝟙 _
      apply WidePullback.hom_ext
      · intro j
        rw [Fin.fin_one_eq_zero j, Category.assoc, cechDiagApp_π, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, cechDiagApp_base, Category.id_comp, WidePullback.π_arrow]
  · ext n : 1
    exact cechDiagApp_base f _

end GlobalTheory.EtC.GmStep
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), ∃ Δ : sch.obj Y ⟶ cech f, IsIso (Δ.app (op ⦋0⦌)) ∧ Δ ≫ cechAug f = sch.map f := by
  first | (exact @GlobalTheory.EtC.GmStep.cechDiag_spec) | (exact GlobalTheory.EtC.GmStep.cechDiag_spec) | (intros; apply GlobalTheory.EtC.GmStep.cechDiag_spec  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.GmStep.DegRow

variable {R : Type} [CommRing R] (F : Shv R)

theorem cobd_disc (P : PSh) (s : (free R).obj ((disc.obj P).obj (op ⦋0⦌)) ⟶ F) :
    cobd (E := disc.obj P) s = 0 := by
  simp [cobd, Fin.sum_univ_two, SimplicialObject.δ]

theorem exists_rep (E : Spc) (x : H R E F 0) : ∃ s : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, IsCls s x := by
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, rfl⟩ := x.mk_surjective
  let b := (z.1 : Cochain ((chains R).obj E) (res R F) 0).v 0 0 (add_zero 0)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v (Cocycle.δ_eq_zero z 1) 0 1 (zero_add 1)
    rw [δ_v 0 1 (zero_add 1) _ 0 1 (zero_add 1) 0 1 (by omega) (zero_add 1),
      (hpos E 1 one_pos).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero] at e
    exact e
  haveI : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  refine ⟨(chainsXIso R E 0).inv ≫ t', z, rfl, ?_⟩
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = 0 := by omega
    change b = (Cochain.single (p := -((0 : ℕ) : ℤ)) (q := 0) ((chainsXIso R E 0).hom ≫ ((chainsXIso R E 0).inv ≫ t') ≫ resι R F) ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 (by simp)
    rw [Cochain.single_v, ← ht']
    simp
  · rcases lt_or_gt_of_ne hp with hp | hp
    · exact (hneg q (by omega)).eq_of_tgt _ _
    · exact (hpos E p hp).eq_of_src _ _

def clsFun (P : PSh) (s : (free R).obj P ⟶ F) : H R (disc.obj P) F 0 :=
  Classical.choose ((isCls_basic R F (disc.obj P) 0).1 s (cobd_disc F P s))

theorem clsFun_spec (P : PSh) (s : (free R).obj P ⟶ F) : IsCls (E := disc.obj P) (n := 0) s (clsFun F P s) :=
  Classical.choose_spec ((isCls_basic R F (disc.obj P) 0).1 s (cobd_disc F P s))

theorem clsFun_eq (P : PSh) (s : (free R).obj P ⟶ F) (x : H R (disc.obj P) F 0)
    (h : IsCls (E := disc.obj P) (n := 0) s x) : clsFun F P s = x :=
  (isCls_basic R F (disc.obj P) 0).2.2.1 s _ _ (clsFun_spec F P s) h

def cls0 (P : PSh) : ((free R).obj P ⟶ F) →+ H R (disc.obj P) F 0 :=
  AddMonoidHom.mk' (clsFun F P) fun s s' =>
    clsFun_eq F P (s + s') _ ((isCls_basic R F (disc.obj P) 0).2.1 s s' _ _ (clsFun_spec F P s) (clsFun_spec F P s'))

theorem degreeZeroClassConstantSpaceAddHom_represents (P : PSh) (s : (free R).obj P ⟶ F) : IsCls (E := disc.obj P) (n := 0) s (cls0 F P s) :=
  clsFun_spec F P s

theorem degreeZeroClassConstantSpaceAddHom_eq_of_represents (P : PSh) (s : (free R).obj P ⟶ F) (x : H R (disc.obj P) F 0)
    (h : IsCls (E := disc.obj P) (n := 0) s x) : cls0 F P s = x :=
  clsFun_eq F P s x h

theorem etaleSpaceCohomologyPullback_degreeZeroClass {P P' : PSh} (f : P ⟶ P') (s : (free R).obj P' ⟶ F) :
    pull R (disc.map f) F 0 (cls0 F P' s) = cls0 F P ((free R).map f ≫ s) :=
  (degreeZeroClassConstantSpaceAddHom_eq_of_represents F P _ _ ((isCls_basic R F (disc.obj P') 0).2.2.2.2 (disc.obj P) (disc.map f) s _ (degreeZeroClassConstantSpaceAddHom_represents F P' s))).symm

theorem degreeZeroClassConstantSpaceAddHom_eq_zero_imp (P : PSh) (s : (free R).obj P ⟶ F) (h : cls0 F P s = 0) : s = 0 :=
  (leray_inj R F (disc.obj P) 0 (fun k m hm hkm _ => by omega)).1 s (h ▸ degreeZeroClassConstantSpaceAddHom_represents F P s)

theorem simplicialSpectralRowDifferential_degreeZeroClass (E : Spc) (p : ℕ) (s : (free R).obj (E.obj (op ⦋p⦌)) ⟶ F) :
    rowD R E F 0 p (cls0 F _ s) = cls0 F _ (cobd s) := by
  simp only [rowD, AddMonoidHom.finset_sum_apply, AddMonoidHom.smul_apply, etaleSpaceCohomologyPullback_degreeZeroClass, cobd, map_sum, map_zsmul]

end GlobalTheory.EtC.GmStep.DegRow

open GlobalTheory.EtC.GmStep.DegRow in

theorem GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
    (∀ (p : ℕ) (s : ℤ), 0 < s → Subsingleton (H R (disc.obj (E.obj (op ⦋p⦌))) F s)) →
    (∀ m : ℤ, 0 < m → Subsingleton (H R E F m)) → ∀ p : ℕ, RowExact R E F 0 p := by
  intro R _ F E hlev htot p y hy
  obtain ⟨s, hs⟩ : ∃ s : (free R).obj (E.obj (op ⦋p + 1⦌)) ⟶ F, IsCls (E := disc.obj (E.obj (op ⦋p + 1⦌))) (n := 0) s y :=
    exists_rep F (disc.obj (E.obj (op ⦋p + 1⦌))) y
  obtain rfl : cls0 F (E.obj (op ⦋p + 1⦌)) s = y := degreeZeroClassConstantSpaceAddHom_eq_of_represents F _ s y hs
  rw [simplicialSpectralRowDifferential_degreeZeroClass] at hy
  have hc : cobd s = 0 := degreeZeroClassConstantSpaceAddHom_eq_zero_imp F _ _ hy
  obtain ⟨x, hx⟩ := (isCls_basic R F E (p + 1)).1 s hc
  have hx0 : x = 0 := @Subsingleton.elim _ (htot _ (by positivity)) x 0
  rw [hx0] at hx
  obtain ⟨t, ht⟩ := (leray_inj R F E p (fun k m hm _ y => @Subsingleton.elim _ (hlev k m (by exact_mod_cast hm)) y 0)).2 s hx
  exact ⟨cls0 F _ t, by rw [simplicialSpectralRowDifferential_degreeZeroClass, ht]⟩

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
  (∀ (p : ℕ) (s : ℤ), 0 < s → Subsingleton (H R (disc.obj (E.obj (op ⦋p⦌))) F s)) →
  (∀ m : ℤ, 0 < m → Subsingleton (H R E F m)) → ∀ p : ℕ, RowExact R E F 0 p := by
  first | (exact @GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (exact GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (intros; apply GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 2 ≤ s → s < n → Subsingleton (Ht q (sp (LaurentPolynomial T)) s i) := by
  first | (exact @GlobalTheory.EtC.laurent_vanishing_finite) | (exact GlobalTheory.EtC.laurent_vanishing_finite) | (intros; apply GlobalTheory.EtC.laurent_vanishing_finite <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem finite_piTensorProduct_const (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A']
    (ι : Type) [Fintype ι] : Module.Finite A (PiTensorProduct A fun _ : ι => A') := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := A')
  refine ⟨⟨Finset.univ.image (fun r : ι → S => PiTensorProduct.tprod A (fun i => (r i : A'))), ?_⟩⟩
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hm : ∀ i, m i ∈ Submodule.span A (S : Set A') := fun i => hS ▸ Submodule.mem_top
  choose c hc using fun i => (Submodule.mem_span_finset).1 (hm i)
  have hm' : m = fun i => ∑ s ∈ S, c i s • s := funext fun i => ((hc i).2).symm
  rw [hm', MultilinearMap.map_sum_finset]
  refine Submodule.sum_mem _ fun r hr => ?_
  rw [MultilinearMap.map_smul_univ]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [Finset.coe_image]
  refine ⟨fun i => ⟨r i, Fintype.mem_piFinset.1 hr i⟩, by simp, rfl⟩

theorem level_vanish : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 2 ≤ s → s < n →
  Subsingleton (Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ n hyp A _ _ hSH hq A' _ _ hfin k s i hs hsn
  obtain ⟨_, e, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  have hT := GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra q n hyp A hSH hq (PiTensorProduct A fun _ : Fin (k + 1) => A')
    (finite_piTensorProduct_const A A' (Fin (k + 1))) s i hs hsn
  haveI : Subsingleton (Ht q (disc.obj (yoneda.obj (Spec (CommRingCat.of
    (LaurentPolynomial (PiTensorProduct A fun _ : Fin (k + 1) => A')))))) s i) := hT
  let f := disc.mapIso e
  have inj : Function.Injective (pull (ZMod q) f.hom (tw q i) s) := fun x y h => by
    have h' := congrArg (pull (ZMod q) f.inv (tw q i) s) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h'
  exact inj.subsingleton

end GlobalTheory.EtC.GmStep
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCechNerve_level_cohomology_subsingleton : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 2 ≤ s → s < n →
  Subsingleton (Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.level_vanish) | (exact GlobalTheory.EtC.GmStep.level_vanish) | (intros; apply GlobalTheory.EtC.GmStep.level_vanish  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem finite_sh_acyclic_twists : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 0 < s → Subsingleton (Ht q (sp T) s i) := by
  intro q _ A _ hA _ T _ _ hfin s i hs
  obtain ⟨hH, hsep⟩ := hA
  obtain ⟨ι, hι, F, hF, hAF, e, hHF, hF'⟩ :=
    GlobalTheory.finite_algebra_strictly_henselian_pi A T
  exact acycF_of_pi_sh (ZMod q) (tw q i) ι F T ⟨e.toRingEquiv⟩
    (fun j => ⟨hHF j, (hF' j).1⟩) s hs

end GlobalTheory.EtC.GmStep
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_strictlyHenselian_tateTwist_acyclic : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 0 < s → Subsingleton (Ht q (sp T) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists) | (exact GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists) | (intros; apply GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem cech_level_acyc : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 0 < s → Subsingleton (Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ A _ hA hq A' _ _ hfin k s i hs
  obtain ⟨e0, -, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI : Subsingleton (Ht q (sp (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) s i) :=
    GlobalTheory.T.finite_strictlyHenselian_tateTwist_acyclic q A hA hq _ inferInstance s i hs
  let f : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌)) :=
    disc.map e0.hom
  let g : disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌)) ⟶ sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) :=
    disc.map e0.inv
  have hgf : g ≫ f = 𝟙 _ := by
    exact (disc.mapIso e0).inv_hom_id
  have hinj : Function.Injective (pull (ZMod q) f (tw q i) s) := by
    intro x y hxy
    have := congrArg (pull (ZMod q) g (tw q i) s) hxy
    rwa [← pull_comp, ← pull_comp, hgf, pull_id, pull_id] at this
  exact hinj.subsingleton

end GlobalTheory.EtC.GmStep
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cohomology_vanishes_positive : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 0 < s → Subsingleton (Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.cech_level_acyc) | (exact GlobalTheory.EtC.GmStep.cech_level_acyc) | (intros; apply GlobalTheory.EtC.GmStep.cech_level_acyc  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.LaurentMapPullbackBijective

theorem laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : LaurentPolynomial A) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  unfold laurentMap
  simp

theorem laurentMap_id (A : Type) [CommRing A] : laurentMap (RingHom.id A) = RingHom.id _ :=
  AddMonoidAlgebra.mapRingHom_id

theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  simp [spMap]

theorem pull_bijective_of_inverse (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (hgf : g.comp f = RingHom.id A) (hfg : f.comp g = RingHom.id B) (n i : ℤ) :
    Function.Bijective (pull _ (spMap f) (tw q i) n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (spMap g) (tw q i) n, fun x => ?_, fun y => ?_⟩
  · rw [← GmPhiNat.pull_spMap_comp, hgf, spMap_id, pull_id]
  · rw [← GmPhiNat.pull_spMap_comp, hfg, spMap_id, pull_id]

theorem ht_subsingleton (q : ℕ) (T : Type) [CommRing T] [Subsingleton T] (n i : ℤ) :
    Subsingleton (Ht q (sp T) n i) := by
  have hb := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q T T n i
  have hfs : RingHom.fst T T = RingHom.snd T T := RingHom.ext fun _ => Subsingleton.elim _ _
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := hb.2 (a, b)
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [hfs] at h1
  exact h1.symm.trans h2

theorem laurent_subsingleton (T : Type) [CommRing T] [Subsingleton T] : Subsingleton (LaurentPolynomial T) := by
  refine subsingleton_of_zero_eq_one ?_
  rw [← map_zero (LaurentPolynomial.C : T →+* LaurentPolynomial T), ← map_one (LaurentPolynomial.C : T →+* LaurentPolynomial T),
    Subsingleton.elim (0 : T) 1]

theorem gmPhi_bijective_of_subsingleton (q : ℕ) (T : Type) [CommRing T] [Subsingleton T] (i : ℤ) :
    Function.Bijective (gmPhi q T i) := by
  haveI := ht_subsingleton q T 0 (i - 1)
  haveI := laurent_subsingleton T
  haveI := ht_subsingleton q (LaurentPolynomial T) 1 i
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem gmPhi_bijective_of_equiv (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {T T' : Type} [CommRing T] [CommRing T']
    (e : T ≃+* T') (hq : IsUnit (q : T)) (i : ℤ) (h : Function.Bijective (gmPhi q T i)) :
    Function.Bijective (gmPhi q T' i) := by
  have hcomm : (gmPhi q T' i) ∘ (pull _ (spMap (e : T →+* T')) _ 0) =
      (pull _ (spMap (laurentMap (e : T →+* T'))) _ 1) ∘ (gmPhi q T i) :=
    funext fun a => (gmPhi_nat h6 q (e : T →+* T') hq i a).symm
  have hgf : (e.symm : T' →+* T).comp (e : T →+* T') = RingHom.id T := by ext; simp
  have hfg : (e : T →+* T').comp (e.symm : T' →+* T) = RingHom.id T' := by ext; simp
  have hpull := pull_bijective_of_inverse q (e : T →+* T') (e.symm : T' →+* T) hgf hfg 0 (i - 1)
  have hpullL := pull_bijective_of_inverse q (laurentMap (e : T →+* T')) (laurentMap (e.symm : T' →+* T))
    (by rw [← GmPhiNat.laurentMap_comp, hgf, laurentMap_id])
    (by rw [← GmPhiNat.laurentMap_comp, hfg, laurentMap_id]) 1 i
  rw [← Function.Bijective.of_comp_iff _ hpull, hcomm]
  exact hpullL.comp h

theorem laurentProd_bijective (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    Function.Bijective ((laurentMap (RingHom.fst T₁ T₂)).prod (laurentMap (RingHom.snd T₁ T₂))) := by
  constructor
  · intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [RingHom.prod_apply] at h1 h2
    apply AddMonoidAlgebra.ext
    refine Finsupp.ext fun n => ?_
    have e1 := congrArg (fun r => r.coeff n) h1
    have e2 := congrArg (fun r => r.coeff n) h2
    simp only [laurentMap_coeff, RingHom.coe_fst, RingHom.coe_snd] at e1 e2
    exact Prod.ext e1 e2
  · rintro ⟨p₁, p₂⟩
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.zipWith Prod.mk (by simp) p₁.coeff p₂.coeff), ?_⟩
    simp only [RingHom.prod_apply]
    refine Prod.ext (AddMonoidAlgebra.ext ?_) (AddMonoidAlgebra.ext ?_)
    · ext n; simp [laurentMap_coeff]
    · ext n; simp [laurentMap_coeff]

theorem gmPhi_bijective_prod (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂]
    (hq : IsUnit (q : T₁ × T₂)) (i : ℤ) (h₁ : Function.Bijective (gmPhi q T₁ i))
    (h₂ : Function.Bijective (gmPhi q T₂ i)) : Function.Bijective (gmPhi q (T₁ × T₂) i) := by
  set f₁ := RingHom.fst T₁ T₂
  set f₂ := RingHom.snd T₁ T₂
  set ψ := (laurentMap f₁).prod (laurentMap f₂)
  have hα := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q T₁ T₂ 0 (i - 1)
  have hγ := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q (LaurentPolynomial T₁) (LaurentPolynomial T₂) 1 i
  have hψ : Function.Bijective ψ := laurentProd_bijective T₁ T₂
  let e := RingEquiv.ofBijective ψ hψ
  have hgf : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := RingHom.ext fun x => e.symm_apply_apply x
  have hfg : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := RingHom.ext fun x => e.apply_symm_apply x
  have hψpull := pull_bijective_of_inverse q e.toRingHom e.symm.toRingHom hgf hfg 1 i
  have he : e.toRingHom = ψ := rfl
  have hl₁ : laurentMap f₁ = (RingHom.fst _ _).comp ψ := rfl
  have hl₂ : laurentMap f₂ = (RingHom.snd _ _).comp ψ := rfl
  let β := fun y : Ht q (sp (LaurentPolynomial (T₁ × T₂))) 1 i =>
    (pull _ (spMap (laurentMap f₁)) _ 1 y, pull _ (spMap (laurentMap f₂)) _ 1 y)
  have hβ : Function.Bijective β := by
    have : β = (fun x : Ht q (sp (LaurentPolynomial T₁ × LaurentPolynomial T₂)) 1 i =>
        (pull _ (spMap (RingHom.fst (LaurentPolynomial T₁) (LaurentPolynomial T₂))) _ 1 x,
          pull _ (spMap (RingHom.snd (LaurentPolynomial T₁) (LaurentPolynomial T₂))) _ 1 x)) ∘
        (pull _ (spMap ψ) _ 1) := by
      funext y
      simp only [β, Function.comp_apply, hl₁, hl₂, GmPhiNat.pull_spMap_comp]
    rw [this]
    rw [he] at hψpull
    exact hγ.comp hψpull
  have hu₁ : IsUnit (q : T₁) := by simpa using hq.map f₁
  have hu₂ : IsUnit (q : T₂) := by simpa using hq.map f₂
  have hcomm : β ∘ (gmPhi q (T₁ × T₂) i) =
      (Prod.map (gmPhi q T₁ i) (gmPhi q T₂ i)) ∘
        (fun x : Ht q (sp (T₁ × T₂)) 0 (i - 1) => (pull _ (spMap f₁) _ 0 x, pull _ (spMap f₂) _ 0 x)) := by
    funext a
    simp only [β, Function.comp_apply, Prod.map_apply]
    rw [gmPhi_nat h6 q f₁ hq i a, gmPhi_nat h6 q f₂ hq i a]
  rw [← Function.Bijective.of_comp_iff' hβ, hcomm]
  exact (h₁.prodMap h₂).comp hα

end GlobalTheory.EtC.LaurentMapPullbackBijective

open GlobalTheory.EtC.LaurentMapPullbackBijective in

theorem GlobalTheory.EtC.GmStep.gmPhi_bijective_finite : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  intro q _ A _ hA hq T _ _ hT
  have h6 : DivisorNaturality := GlobalTheory.T.cup_chern_kummer_pullback_naturality
  have hunit : ∀ (S : Type) [CommRing S] [Algebra A S], IsUnit (q : S) := fun S _ _ => by
    simpa using hq.map (algebraMap A S)
  exact GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction A hA (fun S _ _ => ∀ i : ℤ, Function.Bijective (gmPhi q S i))
    (fun S S' _ _ _ _ e h i => gmPhi_bijective_of_equiv h6 q e.toRingEquiv (hunit S) i (h i))
    (fun S _ _ _ i => gmPhi_bijective_of_subsingleton q S i)
    (fun S₁ S₂ _ _ _ _ _ _ h₁ h₂ i => gmPhi_bijective_prod h6 q S₁ S₂ (hunit (S₁ × S₂)) i (h₁ i) (h₂ i))
    (fun S _ _ _ hS i => GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian q S hS (hunit S) i)
    T hT
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentKummerCupProductMap_bijective_finite_strictHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  first | (exact @GlobalTheory.EtC.GmStep.gmPhi_bijective_finite) | (exact GlobalTheory.EtC.GmStep.gmPhi_bijective_finite) | (intros; apply GlobalTheory.EtC.GmStep.gmPhi_bijective_finite  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.LevelOne

variable {R : Type} [CommRing R]

theorem pull_iso_bijective' {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast (q := q) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem laurentVar_map {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) :
    Units.map (Spec.map (CommRingCat.ofHom (laurentMap f))).appTop.hom.toMonoidHom (laurentVar B) = laurentVar C := by
  ext
  simp only [laurentVar, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  have h := congrArg (fun g => g.hom (LaurentPolynomial.T 1 : LaurentPolynomial B))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (laurentMap f)))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
  rw [laurentMap_T] at h
  exact h.symm

end GlobalTheory.EtC.GmStep.LevelOne

namespace GlobalTheory.EtC.GmStep.LevelOne

theorem rowOne_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (A' : Type) [CommRing A'] [Algebra A A'], Module.Finite A A' → ∀ (k : ℕ) (i : ℤ),
    Function.Bijective (rowOne A A' q i k) := by
  intro q _ A _ hA hq A' _ _ hfin k i
  obtain ⟨e0, e, h1, h2⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI := hfin
  have hT : Module.Finite A (PiTensorProduct A (fun _ : Fin (k + 1) => A')) := inferInstance
  have hr1 := GlobalTheory.T.laurentKummerCupProductMap_bijective_finite_strictHenselian q A hA hq (PiTensorProduct A (fun _ : Fin (k + 1) => A')) hT i
  have hmap1 := congrArg (fun f => disc.map f) h1
  have hmap2 := congrArg (fun f => disc.map f) h2
  simp only [Functor.map_comp] at hmap1 hmap2
  have hqL : IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤)) := by
    have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.comp
      (LaurentPolynomial.C : A →+* LaurentPolynomial A))
    simpa using this
  have hkum : pull _ (disc.map e.hom) (tw q 1) 1 (pull _ (augK A A' k) (tw q 1) 1 (kum q (laurentVar A))) =
      kum q (laurentVar (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) := by
    rw [← pull_comp, augK]
    erw [hmap2]
    have := (GlobalTheory.EtC.a6nat_holds q).2.2.2 (Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A
      (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) (laurentVar A) hqL
    rw [laurentVar_map] at this
    exact this
  have hcst : ∀ a, pull _ (disc.map e.hom) (tw q (i - 1)) 0
      (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q (i - 1)) 0 a) =
      pull _ (spMap (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) (tw q (i - 1)) 0
        (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0 a) := by
    intro a
    rw [← pull_comp, hmap1, pull_comp]
    rfl
  have heq : ∀ a, pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1 (rowOne A A' q i k a) =
      gmPhi q (PiTensorProduct A (fun _ : Fin (k + 1) => A')) i (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0 a) := by
    intro a
    simp only [rowOne, gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [pull_cast, (GlobalTheory.EtC.a6nat_holds q).1, hcst, hkum]
    rfl
  have hcomp : (pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1) ∘ (rowOne A A' q i k) =
      (gmPhi q (PiTensorProduct A (fun _ : Fin (k + 1) => A')) i) ∘ (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0) :=
    funext heq
  have he : Function.Bijective (pull _ (disc.map e.hom : sp (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) ⟶ _) (tw q i) 1) :=
    pull_iso_bijective' (disc.mapIso e) (tw q i) 1
  have he0 : Function.Bijective (pull _ (disc.map e0.hom : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ _) (tw q (i - 1)) 0) :=
    pull_iso_bijective' (disc.mapIso e0) (tw q (i - 1)) 0
  rw [← Function.Bijective.of_comp_iff' he, hcomp]
  exact hr1.comp he0

end GlobalTheory.EtC.GmStep.LevelOne
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_degree_zero_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (i : ℤ), Function.Bijective (rowOne A A' q i k) := by
  first | (exact @GlobalTheory.EtC.GmStep.LevelOne.rowOne_bijective) | (exact GlobalTheory.EtC.GmStep.LevelOne.rowOne_bijective) | (intros; apply GlobalTheory.EtC.GmStep.LevelOne.rowOne_bijective  <;> assumption)
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace GlobalTheory.EtC.GmStep

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem cechC_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] {R : Type} [CommRing R] (F : Shv R) (s : ℤ)
    (k : ℕ) (j : Fin (k + 2)) (y : H R (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) F s) :
    pull R (disc.map ((cechC A A').app (op ⦋k + 1⦌))) F s (pull R (disc.map ((cech (baseHom A A')).δ j)) F s y) =
      pull R (disc.map ((cech (laurentHom A A')).δ j)) F s (pull R (disc.map ((cechC A A').app (op ⦋k⦌))) F s y) := by
  simp only [SimplicialObject.δ]
  rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, (cechC A A').naturality]

theorem aug_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ) (j : Fin (k + 2)) :
    disc.map ((cech (laurentHom A A')).δ j) ≫ augK A A' k = augK A A' (k + 1) := by
  have h := (cechAug (laurentHom A A')).naturality (SimplexCategory.δ j).op
  exact (disc.map_comp _ _).symm.trans (congrArg disc.map (h.trans (Category.comp_id _)))

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using this

theorem rowExact_base (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Finite A A'] (hker : RingHom.ker (algebraMap A A') ≤ nilradical A)
    (j : ℤ) (p : ℕ) : RowExact (ZMod q) (cech (baseHom A A')) (tw q j) 0 p := by
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI, hS⟩ := spec_integral_surj (algebraMap A A') hint hker
  have hB := @GlobalTheory.EtC.b4 q _ _ (baseHom A A') hI hS (isUnit_gamma q A hq) j
  refine GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic (ZMod q) (tw q j) _ (fun k s hs => GlobalTheory.T.cech_cohomology_vanishes_positive q A hA hq A' inferInstance k s j hs) (fun m hm => ?_) p
  haveI : Subsingleton (H (ZMod q) (sch.obj (Spec (CommRingCat.of A))) (tw q j) m) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) m hm
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := (hB m).2 a
    obtain ⟨b', rfl⟩ := (hB m).2 b
    rw [Subsingleton.elim a' b']⟩

theorem gm_vanishing_step : ∀ (q : ℕ) [NeZero q] (n : ℤ), 2 ≤ n → (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
    Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  intro q _ n hn IH A _ _ hA hq i
  suffices h : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨A', _, _, hfin, hker, hx⟩ := GlobalTheory.T.laurent_cohomology_finite_killing q A hA hq n i hn x
  haveI := hfin
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI', hS'⟩ := spec_integral_surj _ (laurentMap_isIntegral _ hint) (laurentMap_ker _ hker)
  have hqL : IsUnit (q : LaurentPolynomial A) := by simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  have hB := @GlobalTheory.EtC.b4 q _ _ (laurentHom A A') hI' hS' (isUnit_gamma q _ hqL) i
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, by omega⟩
  apply (hB N).1
  rw [map_zero]
  obtain ⟨Δ, hΔ0, hΔ⟩ := GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base (laurentHom A A')
  refine GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact (ZMod q) (tw q i) (cech (laurentHom A A')) (yoneda.obj _) Δ hΔ0 N _ ?_ ?_
  · exact (pull_comp (ZMod q) Δ (cechAug (laurentHom A A')) (tw q i) N x).symm.trans
      ((congrArg (fun g => pull (ZMod q) g (tw q i) N x) hΔ).trans hx)
  · intro p hp
    rcases (by omega : (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 0 ∨ (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 1 ∨
        2 ≤ (N : ℤ) - ((p + 1 : ℕ) : ℤ)) with h0 | h1 | h2
    · rw [h0]
      exact rowExact_transfer (fun k => pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0)
        (fun k => GlobalTheory.T.laurentCechNerve_pullback_bijective_degree_zero q A hA hq A' hfin k i) (fun k j y => cechC_face A A' _ _ k j y) p
        (rowExact_base q A hA hq A' hker i p)
    · rw [h1]
      refine rowExact_transfer (fun k => rowOne A A' q i k) (fun k => GlobalTheory.T.cech_degree_zero_bijective q A hA hq A' hfin k i) (fun k j y => ?_) p
        (rowExact_base q A hA hq A' hker (i - 1) p)
      simp only [rowOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [pull_cast, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1, cechC_face,
        ← pull_comp (ZMod q) (disc.map ((cech (laurentHom A A')).δ j)) (augK A A' k), aug_face]
    · intro y _
      haveI := GlobalTheory.T.laurentCechNerve_level_cohomology_subsingleton q N IH A hA hq A' hfin (p + 1) _ i h2 (by omega)
      exact ⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩

end GlobalTheory.EtC.GmStep

end
end
