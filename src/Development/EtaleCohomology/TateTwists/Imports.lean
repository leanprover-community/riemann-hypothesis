import Development.EtaleCohomology.TateTwists.EtaleCochainSemilinearMapCompCompatible
import Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationExistsOfEvalua
import Development.EtaleCohomology.KummerTheory.CupAWCutEv
import Development.EtaleCohomology.TateTwists.EtaleChainCochainEvalDifferentialFormulaHolds

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSemilinearCohomologyOperationImageSpec : Prop :=
  ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
    (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
    ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β

namespace OpCompPf

theorem ev_comp_ofHom {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  simp only [ev, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

noncomputable def invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) : SemiMap J I where
  app U s := (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm.toAddMonoidHom
  nat {V U} g s a := by
    apply (hb V s).1
    have h1 := ρ.nat g s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app V s ((AddEquiv.ofBijective (ρ.app V s) (hb V s)).symm (Sec.res g a)) = Sec.res g a :=
      (AddEquiv.ofBijective (ρ.app V s) (hb V s)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    rw [h3, ← h1, h2]
  comm U s t a := by
    apply (hb U t).1
    have h1 := ρ.comm U s t ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a)
    have h2 : ρ.app U s ((AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm a) = a :=
      (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a
    have h3 : ρ.app U t ((AddEquiv.ofBijective (ρ.app U t) (hb U t)).symm (Sec.map (J.d s t) a)) = Sec.map (J.d s t) a :=
      (AddEquiv.ofBijective (ρ.app U t) (hb U t)).apply_symm_apply _
    simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    rw [h3, ← h1, h2]

theorem invMap_app {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (J.X s) U) :
    ρ.app U s ((invMap ρ hb).app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).apply_symm_apply a

theorem app_invMap {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J)
    (hb : ∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (ρ.app U s)) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) :
    (invMap ρ hb).app U s (ρ.app U s a) = a :=
  (AddEquiv.ofBijective (ρ.app U s) (hb U s)).symm_apply_apply a

end OpCompPf

open OpCompPf in
theorem etale_cohomology_operation_comp_of_image_spec (hspec : EtaleSemilinearCohomologyOperationImageSpec) : EtaleCochainSemilinearMapCompCompatible := by
  intro S R _ _ I J J' ρ ρ' u hu
  constructor
  · intro E n x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
    rw [(hspec S R ρ).2 E n α β hβ, cpost_mk]
    apply (hspec S R ρ').2
    intro p s h U y
    show ev (β.1.comp (Cochain.ofHom u) (add_zero n)) p s h U y = _
    rw [ev_comp_ofHom, hβ p s h U y, hu]
  · intro hb E n
    let σ := invMap ρ hb
    rw [Function.bijective_iff_has_inverse]
    refine ⟨σ.op.app E n, ?_, ?_⟩
    · intro x
      obtain ⟨α, rfl⟩ := x.mk_surjective
      obtain ⟨β, hβ⟩ := (hspec S R ρ).1 E n α
      rw [(hspec S R ρ).2 E n α β hβ]
      apply (hspec R S σ).2
      intro p s h U y
      rw [hβ p s h U y]
      exact (app_invMap ρ hb U s _).symm
    · intro x
      obtain ⟨β, rfl⟩ := x.mk_surjective
      obtain ⟨γ, hγ⟩ := (hspec R S σ).1 E n β
      rw [(hspec R S σ).2 E n β γ hγ]
      apply (hspec S R ρ).2
      intro p s h U y
      rw [hγ p s h U y]
      exact (invMap_app ρ hb U s _).symm

end LateralTheory.EtaleFoundations
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_semilinear_cohomology_operation_image_spec_of_hyp
    (hImage₂ : ∀ (S R : Type) [CommRing S] [CommRing R] {I : Cx S} {J : Cx R} (ρ : SemiMap I J),
      (∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n), ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1) ∧
      ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
        ρ.IsImage α.1 β.1 → ρ.op.app E n (CohomologyClass.mk α) = CohomologyClass.mk β) :
    EtaleSemilinearCohomologyOperationImageSpec :=
  hImage₂

end LateralTheory.EtaleFoundations
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvBasicPf
variable {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
open LateralTheory.KummerTheory.AW

theorem ev_sub (α β : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  rw [ev_eq, Cochain.sub_v, Preadditive.comp_sub]
  exact map_sub (AddMonoidHom.mk' (fun φ : _ ⟶ I.X s => Sec.map φ (freeGen R _ U x)) (fun _ _ => rfl)) _ _

theorem ev_zero (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  rw [ev_eq, Cochain.zero_v, comp_zero]
  exact map_zero (AddMonoidHom.mk' (fun φ : _ ⟶ I.X s => Sec.map φ (freeGen R _ U x)) (fun _ _ => rfl))

theorem ev_zsmul (c : ℤ) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (c • α) p s h U x = c • ev α p s h U x := by
  exact map_zsmul (AddMonoidHom.mk' (fun β : Cochain ((chains R).obj E) I n => ev β p s h U x)
    (fun a b => ev_add a b p s h U x)) c α

theorem ev_post {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  rw [ev_eq, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ev_eq]; rfl

theorem chainsXIso_nat {E' : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  rw [Iso.inv_comp_eq]
  unfold chains chainsXIso
  change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(p : ℤ)) = _
  exact HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl

theorem ev_pre {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  rw [ev_eq, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, reassoc_of% (chainsXIso_nat (R := R) f p), ev_eq]
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map (f.app (op (SimplexCategory.mk p))))
    (freeGen R _ U x)) = _
  rw [map_freeGen]; rfl

end LateralTheory.EtaleFoundations.EvBasicPf

open LateralTheory.EtaleFoundations.EvBasicPf LateralTheory.KummerTheory.AW in
theorem LateralTheory.EtaleFoundations.pp_ev_basic_of : LateralTheory.EtaleFoundations.pp_ev_basic := fun _ _ =>
  ⟨fun α β p s h U x => ⟨ev_add α β p s h U x, ev_sub α β p s h U x, ev_zero p s h U x, fun c => ev_zsmul c α p s h U x⟩,
   fun α p s h _ _ g x => ev_res α p s h g x,
   fun α β hh => ev_ext α β hh,
   fun f α p s h U x => ev_pre f α p s h U x,
   fun m α p s h U x => ev_post m α p s h U x⟩
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvMkPf

variable {R : Type} [CommRing R] {E : Spc} {I : Cx R}

theorem sq {X Y : Type 1} (h : X ⟶ Y) {M N : ModuleCat.{1} (ULift.{1} R)} (a : Y ⟶ M) (b : X ⟶ N) (φ : N ⟶ M)
    (H : ∀ x, a (h x) = φ (b x)) :
    (ModuleCat.free (ULift.{1} R)).map h ≫ ModuleCat.freeDesc a = ModuleCat.freeDesc b ≫ φ := by
  apply ModuleCat.free_hom_ext
  intro x
  simp [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, H]

noncomputable def eta (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    (freeP R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (I.X s).obj where
  app U := ModuleCat.freeDesc (X := ULift.{1} (Sx E k U.unop)) (↾fun x => F U.unop (ULift.down x))
  naturality U V g := sq _ _ _ _ (fun x => (hF V.unop U.unop g.unop x.down).symm)

noncomputable def phi (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) (I.X s)).symm (eta k s F hF)

theorem phi_unit (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    toSheafify Scheme.etaleTopology.{0} ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) ≫ (phi k s F hF).hom =
      eta k s F hF := by
  have := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) (I.X s)).apply_symm_apply (eta k s F hF)
  rw [Adjunction.homEquiv_unit] at this
  exact this

theorem phi_freeGen (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g))
    (U : Scheme.{0}) (x : Sx E k U) :
    ((phi k s F hF).hom.app (op U)).hom (freeGen R _ U x) = F U x := by
  have h2 := congrArg (fun f => (f.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) (phi_unit k s F hF)
  exact h2.trans (ModuleCat.freeDesc_apply _ _)

variable {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
  (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))

noncomputable def comp (p q : ℤ) (hpq : p + n = q) : ((chains R).obj E).X p ⟶ I.X q :=
  if hp : p ≤ 0 then
    (HomologicalComplex.XIsoOfEq _ (by omega : p = -((p.natAbs : ℕ) : ℤ))).hom ≫ (chainsXIso R E p.natAbs).hom ≫
      phi p.natAbs q (fun U x => a p.natAbs q (by omega) U x) (fun V U g x => ha _ _ _ V U g x)
  else 0

theorem aux {s : ℤ} (j k : ℕ) (e : j = k) (hjk : -(k : ℤ) = -(j : ℤ)) (hj : -(j : ℤ) + n = s) (hk : -(k : ℤ) + n = s) :
    (HomologicalComplex.XIsoOfEq ((chains R).obj E) hjk).hom ≫ (chainsXIso R E j).hom ≫
      phi j s (fun U x => a j s hj U x) (fun V U g x => ha _ _ _ V U g x) =
    (chainsXIso R E k).hom ≫ phi k s (fun U x => a k s hk U x) (fun V U g x => ha _ _ _ V U g x) := by
  subst e
  simp

theorem comp_neg (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) :
    comp a ha (-(k : ℤ)) s h = (chainsXIso R E k).hom ≫ phi k s (fun U x => a k s h U x) (fun V U g x => ha _ _ _ V U g x) := by
  unfold comp
  rw [dif_pos (by omega)]
  exact aux a ha _ _ (by omega) _ _ _

end LateralTheory.EtaleFoundations.EvMkPf

open LateralTheory.EtaleFoundations.EvMkPf in
theorem LateralTheory.EtaleFoundations.pp_ev_mk_of : LateralTheory.EtaleFoundations.pp_ev_mk := by
  intro R _ E I n a ha
  refine ⟨Cochain.mk (comp a ha), fun p s h U x => ?_⟩
  unfold ev
  rw [Cochain.mk_v, comp_neg a ha p s h, Iso.inv_hom_id_assoc]
  exact phi_freeGen _ _ _ _ U x
end

section
theorem LateralTheory.EtaleFoundations.pp_ev_delta_of : LateralTheory.EtaleFoundations.pp_ev_delta :=
  LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds
end

section
namespace LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
theorem etale_evaluation_map_basic_of_components : LateralTheory.EtaleFoundations.pp_ev_basic := by
  apply LateralTheory.EtaleFoundations.pp_ev_basic_of
theorem etale_cohomology_evaluation_mk : LateralTheory.EtaleFoundations.pp_ev_mk := by
  apply LateralTheory.EtaleFoundations.pp_ev_mk_of
theorem etale_cohomology_evaluation_connecting_hom : LateralTheory.EtaleFoundations.pp_ev_delta := by
  apply LateralTheory.EtaleFoundations.pp_ev_delta_of
theorem etale_torsion_cohomology_operation_spec : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  apply LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation <;> first | exact etale_evaluation_map_basic_of_components | exact etale_cohomology_evaluation_mk | exact etale_cohomology_evaluation_connecting_hom
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := etale_torsion_cohomology_operation_spec
end LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses
end

section
theorem LateralTheory.Fix.EtaleCochainSemilinearMapCompCompatible.intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapCompCompatible :=
  LateralTheory.EtaleFoundations.etale_cohomology_operation_comp_of_image_spec
    (LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_image_spec_of_hyp (by
      have h := LateralTheory.Fin.EtaleCochainSemilinearMapOnClasses.intersectionNumber_baseChange
      unfold LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses at h
      exact h))
end
