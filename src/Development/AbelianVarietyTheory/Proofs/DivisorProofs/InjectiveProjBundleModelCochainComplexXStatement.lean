import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SxProdIsoHomSnd

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.CotSheaf

open CupSpec

variable {R : Type} [CommRing R] {q N : ℕ} {I : Cx R} {n : ℤ}

def fstHom {U W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj U ⨯ E) p W) : W ⟶ U := y.map prod.fst

theorem fstHom_pair {U W : Scheme.{0}} {E : Spc} {p : ℕ} (v : W ⟶ U) (b : Sx E p W) :
    fstHom (sxPair (schSx v p) b) = v := sxPair_fst _ _

theorem fstHom_res {U W W' : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj U ⨯ E) p W) (w : W' ⟶ W) :
    fstHom (y.res w) = w ≫ fstHom y := by
  rw [fstHom, sxMap_res]; rfl

theorem fstHom_map {U Y W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj Y ⨯ E) p W) (g : Y ⟶ U) :
    fstHom (y.map (prod.map (sch.map g) (𝟙 E))) = fstHom y ≫ g := by
  rw [fstHom, ← sxMap_comp, prod.map_fst, sxMap_comp]; rfl

theorem snd_map {U Y W : Scheme.{0}} {E : Spc} {p : ℕ} (y : Sx (sch.obj Y ⨯ E) p W) (g : Y ⟶ U) :
    (y.map (prod.map (sch.map g) (𝟙 E))).map prod.snd = y.map prod.snd := by
  rw [← sxMap_comp, prod.map_snd, Category.comp_id]

theorem sx_res_res {E : Spc} {p : ℕ} {U V W : Scheme.{0}} (x : Sx E p U) (f : V ⟶ U) (g : W ⟶ V) :
    (x.res f).res g = x.res (g ≫ f) := by
  change _ = (E.obj (op (SimplexCategory.mk p))).map (g ≫ f).op x
  rw [op_comp, FunctorToTypes.map_comp_apply]; rfl

theorem ev_res_pair {U W W' : Scheme.{0}} (α : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (y : Sx (sch.obj U ⨯ fibQ q N) p W) (w : W' ⟶ W) :
    Sec.res w (ev α p s h W y) =
      ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (((cotPre R q N I n).map (w ≫ fstHom y).op).hom α) p s h W'
        (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
  rw [ev_res, cotPre_ev]
  congr 1
  apply sx_prod_ext
  · rw [sxPair_map, sxPair_fst, sxMap_res, schSx_map, Category.id_comp]
    rfl
  · rw [sxMap_res, sxPair_map, sxPair_snd]
    rfl

end GlobalTheory.EtC.CotSheaf

namespace GlobalTheory.EtC

open CupSpec CotSheaf

theorem cotPre_isSheaf (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) :
    Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R))), isSheaf_iff_isSheaf_of_type]
  have hI : ∀ s : ℤ, Presieve.IsSheaf Scheme.etaleTopology.{0} ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    fun s => (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 (I.X s).cond)
  have sep : ∀ (s : ℤ) (W : Scheme.{0}) (T : Sieve W), T ∈ Scheme.etaleTopology.{0} W → ∀ t t' : Sec (I.X s) W,
      (∀ (W' : Scheme.{0}) (w : W' ⟶ W), T w → Sec.res w t = Sec.res w t') → t = t' :=
    fun s W T hT t t' ht => (hI s T hT).isSeparatedFor.ext fun _ w hw => ht _ w hw
  intro U S hS c hc
  rw [Presieve.compatible_iff_sieveCompatible] at hc
  have hC : ∀ {Y Z : Scheme.{0}} (f : Y ⟶ U) (g : Z ⟶ Y) (hf : S f),
      ((cotPre R q N I n).map g.op).hom (c f hf) = c (g ≫ f) (S.downward_closed hf g) := fun f g hf => (hc f g hf).symm

  have hcong : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W : Scheme.{0}} (g g' : W ⟶ U) (hg : S g) (hg' : S g')
      (x x' : Sx (fibQ q N) p W), g = g' → x = x' →
      ev (I := I) (E := sch.obj W ⨯ fibQ q N) (c g hg) p s h W (sxPair (schSx (𝟙 W) p) x) =
        ev (I := I) (E := sch.obj W ⨯ fibQ q N) (c g' hg') p s h W (sxPair (schSx (𝟙 W) p) x') := by
    rintro p s h W g _ hg hg' x _ rfl rfl; rfl

  have hL : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W W' : Scheme.{0}} (g : W ⟶ U) (hg : S g)
      (x : Sx (fibQ q N) p W) (t : W' ⟶ W),
      Sec.res t (ev (I := I) (E := sch.obj W ⨯ fibQ q N) (c g hg) p s h W (sxPair (schSx (𝟙 W) p) x)) =
        ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (t ≫ g) (S.downward_closed hg t)) p s h W'
          (sxPair (schSx (𝟙 W') p) (x.res t)) := by
    intro p s h W W' g hg x t
    refine (ev_res_pair (c g hg) p s h _ t).trans ?_
    rw [fstHom_pair, Category.comp_id, hC, sxPair_snd]

  have hAm : ∀ γ : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n,
      (∀ {Y : Scheme.{0}} (g : Y ⟶ U) (hg : S g), ((cotPre R q N I n).map g.op).hom γ = c g hg) →
      ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {W W' : Scheme.{0}} (y : Sx (sch.obj U ⨯ fibQ q N) p W) (w : W' ⟶ W)
        (hw : S (w ≫ fstHom y)),
      Sec.res w (ev γ p s h W y) = ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
    intro γ hγ p s h W W' y w hw
    refine (ev_res_pair γ p s h y w).trans ?_
    rw [hγ]

  have key : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0}) (y : Sx (sch.obj U ⨯ fibQ q N) p W),
      ∃ t : Sec (I.X s) W, ∀ (W' : Scheme.{0}) (w : W' ⟶ W) (hw : S (w ≫ fstHom y)),
        Sec.res w t = ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w)) := by
    intro p s h W y
    let fam : Presieve.FamilyOfElements ((I.X s).obj ⋙ forget (ModuleCat.{1} (ULift.{1} R)))
        (S.pullback (fstHom y)).arrows := fun W' w hw =>
      ev (I := I) (E := sch.obj W' ⨯ fibQ q N) (c (w ≫ fstHom y) hw) p s h W'
          (sxPair (schSx (𝟙 W') p) ((y.map prod.snd).res w))
    have hfam : fam.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro Y Z f g hf
      refine Eq.trans ?_ (hL p s h (f ≫ fstHom y) hf _ g).symm
      exact hcong _ _ _ _ _ _ _ _ _ (Category.assoc _ _ _) (sx_res_res _ _ _).symm
    obtain ⟨t, ht, -⟩ := hI s _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom y) hS) fam hfam
    exact ⟨t, fun W' w hw => ht w hw⟩
  choose a ha using key
  have hnat : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (V W : Scheme.{0}) (g : V ⟶ W)
      (y : Sx (sch.obj U ⨯ fibQ q N) p W), Sec.res g (a p s h W y) = a p s h V (y.res g) := by
    intro p s h V W g y
    apply sep s V _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom (y.res g)) hS)
    intro W' w hw
    have hw' : S ((w ≫ g) ≫ fstHom y) := by
      rw [fstHom_res] at hw; simpa [Category.assoc] using hw
    rw [secRes_res, ha p s h W y W' (w ≫ g) hw', ha p s h V (y.res g) W' w hw]
    refine hcong _ _ _ _ _ _ _ _ _ ?_ ?_
    · rw [fstHom_res, Category.assoc]
    · rw [sxMap_res, sx_res_res]
  obtain ⟨α, hα⟩ := ev_exists (R := R) (E := sch.obj U ⨯ fibQ q N) (I := I) (n := n) a hnat
  have hαam : ∀ {Y : Scheme.{0}} (g : Y ⟶ U) (hg : S g), ((cotPre R q N I n).map g.op).hom α = c g hg := by
    intro Y g hg
    apply ev_ext
    intro p s h W y
    rw [cotPre_ev, hα]
    apply sep s W _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom (y.map (prod.map (sch.map g) (𝟙 _)))) hS)
    intro W' w hw
    rw [ha p s h W _ W' w hw]
    refine Eq.trans ?_ (ev_res_pair (c g hg) p s h y w).symm
    rw [hC, snd_map]
    refine hcong _ _ _ _ _ _ _ _ _ ?_ rfl
    rw [fstHom_map, Category.assoc]
  refine ⟨α, fun Y g hg => hαam g hg, fun β hβ => ?_⟩
  apply ev_ext
  intro p s h W y
  apply sep s W _ (Scheme.etaleTopology.{0}.pullback_stable (fstHom y) hS)
  intro W' w hw
  rw [hAm β (fun g hg => hβ g hg) p s h y w hw, hAm α (fun g hg => hαam g hg) p s h y w hw]

end GlobalTheory.EtC

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSheaf_projBundleCochainPresheaf_etale : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ), Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := by
  first | (exact @GlobalTheory.EtC.cotPre_isSheaf) | (exact GlobalTheory.EtC.cotPre_isSheaf) | (intros; apply GlobalTheory.EtC.cotPre_isSheaf  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.NatFamExt

variable {R : Type} [CommRing R] (P : PSh)

def finMap {F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} {V W : Scheme.{0}ᵒᵖ} (g : V ⟶ W) :
    (P.obj V →₀ F.obj V) →ₗ[ULift.{1} R] (P.obj W →₀ F.obj W) :=
  Finsupp.lmapDomain (F.obj W) (ULift.{1} R) (P.map g) ∘ₗ Finsupp.mapRange.linearMap (F.map g).hom

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] (P : _root_.GlobalTheory.EtC.PSh) in
theorem _root_.GlobalTheory.NatFamExt.finMap_single {F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)}
    {V W : Scheme.{0}ᵒᵖ} (g : V ⟶ W) (x : P.obj V) (a : F.obj V) :
    _root_.GlobalTheory.NatFamExt.finMap P g (Finsupp.single x a) =
      Finsupp.single (P.map g x) ((F.map g).hom a) := by
  simp [_root_.GlobalTheory.NatFamExt.finMap, Finsupp.mapDomain_single]

def finP (F : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj V := ModuleCat.of _ (P.obj V →₀ F.obj V)
  map g := ModuleCat.ofHom (finMap P g)
  map_id V := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change finMap P (𝟙 V) (Finsupp.single x a) = Finsupp.single x a
    rw [finMap_single]
    simp
  map_comp f g := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change finMap P (f ≫ g) (Finsupp.single x a) = finMap P g (finMap P f (Finsupp.single x a))
    rw [finMap_single, finMap_single, finMap_single]
    simp

def finPMap {F F' : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (φ : F ⟶ F') : finP P F ⟶ finP P F' where
  app V := ModuleCat.ofHom (Finsupp.mapRange.linearMap (φ.app V).hom)
  naturality V W g := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change Finsupp.mapRange.linearMap (φ.app W).hom (finMap P g (Finsupp.single x a)) =
      finMap P g (Finsupp.mapRange.linearMap (φ.app V).hom (Finsupp.single x a))
    rw [finMap_single, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_single, finMap_single]
    exact congrArg _ (congrArg (fun h => h.hom a) (φ.naturality g))

def famHom (G : Shv R) {A : Shv R} (ψ : ∀ V : Scheme.{0}, P.obj (op V) → Sec A V →ₗ[ULift.{1} R] Sec G V)
    (hψ : ∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (a : Sec A V),
      Sec.res w (ψ V x a) = ψ W (P.map w.op x) (Sec.res w a)) :
    finP P A.obj ⟶ G.obj where
  app V := ModuleCat.ofHom (Finsupp.lsum (ULift.{1} R) (ψ V.unop))
  naturality V W g := by
    refine ModuleCat.hom_ext (Finsupp.lhom_ext fun x a => ?_)
    change Finsupp.lsum (ULift.{1} R) (ψ W.unop) (finMap P g (Finsupp.single x a)) =
      (G.obj.map g).hom (Finsupp.lsum (ULift.{1} R) (ψ V.unop) (Finsupp.single x a))
    rw [finMap_single, Finsupp.lsum_single, Finsupp.lsum_single]
    exact (hψ _ _ g.unop x a).symm

end GlobalTheory.NatFamExt

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.natFam_extend_of_injective : ∀ (R : Type) [CommRing R] (P : _root_.GlobalTheory.EtC.PSh)
    (G : _root_.GlobalTheory.EtC.Shv R), Injective G → ∀ {A B : _root_.GlobalTheory.EtC.Shv R} (f : A ⟶ B), Mono f →
    ∀ (ψ : ∀ V : Scheme.{0}, P.obj (op V) →
      _root_.GlobalTheory.EtC.Sec A V →ₗ[ULift.{1} R] _root_.GlobalTheory.EtC.Sec G V),
    (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (a : _root_.GlobalTheory.EtC.Sec A V),
      _root_.GlobalTheory.EtC.Sec.res w (ψ V x a) = ψ W (P.map w.op x) (_root_.GlobalTheory.EtC.Sec.res w a)) →
    ∃ χ : ∀ V : Scheme.{0}, P.obj (op V) →
      _root_.GlobalTheory.EtC.Sec B V →ₗ[ULift.{1} R] _root_.GlobalTheory.EtC.Sec G V,
      (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (b : _root_.GlobalTheory.EtC.Sec B V),
        _root_.GlobalTheory.EtC.Sec.res w (χ V x b) = χ W (P.map w.op x) (_root_.GlobalTheory.EtC.Sec.res w b)) ∧
      ∀ (V : Scheme.{0}) (x : P.obj (op V)) (a : _root_.GlobalTheory.EtC.Sec A V),
        χ V x (_root_.GlobalTheory.EtC.Sec.map f a) = ψ V x a := by
  intro R _ P G hG A B f hf ψ hψ
  have hfval : Mono f.hom := (sheafToPresheaf _ _).map_mono f
  have hinj : ∀ V, Function.Injective (f.hom.app V).hom := fun V =>
    (ModuleCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app f.hom).1 hfval V)
  haveI : Injective G.obj :=
    Injective.injective_of_adjoint (sheafificationAdjunction Scheme.etaleTopology _) G
  haveI : Mono (_root_.GlobalTheory.NatFamExt.finPMap P f.hom) := by
    rw [NatTrans.mono_iff_mono_app]
    intro V
    rw [ModuleCat.mono_iff_injective]
    exact Finsupp.mapRange_injective _ (map_zero _) (hinj V)
  obtain ⟨θ, hθ⟩ := Injective.factors (_root_.GlobalTheory.NatFamExt.famHom P G ψ hψ)
    (_root_.GlobalTheory.NatFamExt.finPMap P f.hom)
  refine ⟨fun V x => (θ.app (op V)).hom ∘ₗ Finsupp.lsingle x, ?_, ?_⟩
  · intro V W w x b
    have h := congrArg (fun h => h.hom (Finsupp.single x b)) (θ.naturality w.op)
    change (θ.app (op W)).hom (_root_.GlobalTheory.NatFamExt.finMap P w.op (Finsupp.single x b)) =
      (G.obj.map w.op).hom ((θ.app (op V)).hom (Finsupp.single x b)) at h
    rw [_root_.GlobalTheory.NatFamExt.finMap_single] at h
    exact h.symm
  · intro V x a
    have h := congrArg (fun h => (h.app (op V)).hom (Finsupp.single x a)) hθ
    change (θ.app (op V)).hom
        (Finsupp.mapRange.linearMap (f.hom.app (op V)).hom (Finsupp.single x a)) =
      Finsupp.lsum (ULift.{1} R) (ψ V) (Finsupp.single x a) at h
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.lsum_single] at h
    exact h
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natural_sections_linear_extension : ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R), Injective G → ∀ {A B : Shv R} (f : A ⟶ B), Mono f → ∀ (ψ : ∀ V : Scheme.{0}, P.obj (op V) → Sec A V →ₗ[ULift.{1} R] Sec G V), (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (a : Sec A V), Sec.res w (ψ V x a) = ψ W (P.map w.op x) (Sec.res w a)) → ∃ χ : ∀ V : Scheme.{0}, P.obj (op V) → Sec B V →ₗ[ULift.{1} R] Sec G V, (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (b : Sec B V), Sec.res w (χ V x b) = χ W (P.map w.op x) (Sec.res w b)) ∧ ∀ (V : Scheme.{0}) (x : P.obj (op V)) (a : Sec A V), χ V x (Sec.map f a) = ψ V x a := by
  first | (exact @GlobalTheory.natFam_extend_of_injective) | (exact GlobalTheory.natFam_extend_of_injective) | (intros; apply GlobalTheory.natFam_extend_of_injective  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC
open CupSpec

variable {R : Type} [CommRing R]

section Build
variable (q N : ℕ) (I : Cx R) (n : ℤ) {B : Shv R}
  (χ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ V : Scheme.{0}, Sx (fibQ q N) p V → Sec B V →ₗ[ULift.{1} R] Sec (I.X s) V)
  (hχ : ∀ p s h (V W : Scheme.{0}) (w : W ⟶ V) (x : Sx (fibQ q N) p V) (b : Sec B V),
      Sec.res w (χ p s h V x b) = χ p s h W (x.res w) (Sec.res w b))
include hχ in
theorem buildC_exists (U : Scheme.{0}) (b : Sec B U) :
    ∃ α : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n, ∀ p s h W y,
      ev α p s h W y = χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b) := by
  refine ev_exists _ (fun p s h W W' g y => ?_)
  rw [hχ, secRes_res, sxMap_res, sxMap_res]
  rfl

def cochainOfSection (U : Scheme.{0}) (b : Sec B U) : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n :=
  (buildC_exists q N I n χ hχ U b).choose

theorem buildC_ev (U : Scheme.{0}) (b : Sec B U) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (W : Scheme.{0})
    (y : Sx (sch.obj U ⨯ fibQ q N) p W) :
    ev (cochainOfSection q N I n χ hχ U b) p s h W y = χ p s h W (y.map prod.snd) (Sec.res (show W ⟶ U from y.map prod.fst) b) :=
  (buildC_exists q N I n χ hχ U b).choose_spec p s h W y

def buildMor : B.obj ⟶ cotPre R q N I n where
  app U := ModuleCat.ofHom
    { toFun := cochainOfSection q N I n χ hχ U.unop
      map_add' := fun b b' => ev_ext _ _ (fun p s h W y => by
        rw [ev_add, buildC_ev, buildC_ev, buildC_ev, Sec.res, Sec.res, Sec.res, map_add, map_add])
      map_smul' := fun r b => ev_ext _ _ (fun p s h W y => by
        rw [RingHom.id_apply, ev_smulU, buildC_ev, buildC_ev, Sec.res, Sec.res, map_smul, map_smul]) }
  naturality U U' g := by
    ext b : 2
    refine ev_ext _ _ (fun p s h W y => ?_)
    change ev (cochainOfSection q N I n χ hχ U'.unop (Sec.res g.unop b)) p s h W y =
      ev (((cotPre R q N I n).map g.unop.op).hom (cochainOfSection q N I n χ hχ U.unop b)) p s h W y
    have e2 := ev_pull (I := I) (prod.map (sch.map g.unop) (𝟙 (fibQ q N))) (cochainOfSection q N I n χ hχ U.unop b) p s h W y
    refine Eq.trans ?_ e2.symm
    rw [buildC_ev, buildC_ev, secRes_res, ← sxMap_comp, ← sxMap_comp, prod.map_snd, prod.map_fst, Category.comp_id]
    rfl

end Build

theorem injective_cotSheaf (q N : ℕ) (I : Cx R) (hI : ∀ m, Injective (I.X m)) (n : ℤ)
    (hS : Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n)) :
    Injective (⟨cotPre R q N I n, hS⟩ : Shv R) := by
  constructor
  intro A B g f hf
  let ψ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ V : Scheme.{0}, Sx (fibQ q N) p V → Sec A V →ₗ[ULift.{1} R] Sec (I.X s) V :=
    fun p s h V x => (evLin I _ n p s h V (sxPair (schSx (𝟙 V) p) x)).comp (g.hom.app (op V)).hom
  have hψ : ∀ p s h (V W : Scheme.{0}) (w : W ⟶ V) (x : Sx (fibQ q N) p V) (a : Sec A V),
      Sec.res w (ψ p s h V x a) = ψ p s h W (x.res w) (Sec.res w a) := by
    intro p s h V W w x a
    have hn : (g.hom.app (op W)).hom (Sec.res w a) = ((cotPre R q N I n).map w.op).hom ((g.hom.app (op V)).hom a) :=
      ConcreteCategory.congr_hom (g.hom.naturality w.op) a
    refine (ev_res (E := sch.obj V ⨯ fibQ q N) (I := I) ((g.hom.app (op V)).hom a) p s h w _).trans ?_
    refine Eq.trans ?_ (congrArg (fun c => ev (E := sch.obj W ⨯ fibQ q N) (I := I) c p s h W
      (sxPair (schSx (𝟙 W) p) (x.res w))) hn).symm
    have e2 := ev_pull (I := I) (prod.map (sch.map w) (𝟙 (fibQ q N))) ((g.hom.app (op V)).hom a) p s h W
      (sxPair (schSx (𝟙 W) p) (x.res w))
    refine Eq.trans ?_ e2.symm
    rw [sxPair_res, sxPair_map]
    congr 2
  have hχ := fun p s h => GlobalTheory.T.natural_sections_linear_extension R ((fibQ q N).obj (op (SimplexCategory.mk p))) (I.X s) (hI s) f hf (ψ p s h) (hψ p s h)
  choose χ hχn hχf using hχ
  refine ⟨⟨buildMor q N I n χ hχn⟩, ?_⟩
  ext U a : 4
  refine LinearMap.ext fun a => ?_
  change cochainOfSection q N I n χ hχn U.unop (Sec.map f a) = (g.hom.app U).hom a
  refine ev_ext _ _ (fun p s h W y => ?_)
  refine (buildC_ev q N I n χ hχn U.unop (Sec.map f a) p s h W y).trans ?_
  refine (congrArg (χ p s h W (y.map prod.snd)) (map_res f (show W ⟶ U.unop from y.map prod.fst) a)).trans ?_
  refine (hχf p s h W _ _).trans ?_
  have hn := ConcreteCategory.congr_hom (g.hom.naturality (show W ⟶ U.unop from y.map prod.fst).op) a
  refine (congrArg (fun c => ev (E := sch.obj W ⨯ fibQ q N) (I := I) c p s h W
    (sxPair (schSx (𝟙 W) p) (y.map prod.snd))) hn).trans ?_
  refine (ev_pull (I := I) (prod.map (sch.map (show W ⟶ U.unop from y.map prod.fst)) (𝟙 (fibQ q N)))
    ((g.hom.app U).hom a) p s h W _).trans ?_
  congr 1
  rw [sxPair_map]
  exact sxPair_eta y

theorem Jcx_X_injective : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), (∀ n, CategoryTheory.Injective (I.X n)) →
    ∀ n, CategoryTheory.Injective ((Jcx R q N I).X n) := by
  intro R _ q N I hI n
  have hS := GlobalTheory.T.isSheaf_projBundleCochainPresheaf_etale R q N I n
  exact Injective.of_iso (sheafificationIso (⟨cotPre R q N I n, hS⟩ : Shv R)) (injective_cotSheaf q N I hI n hS)

end GlobalTheory.EtC

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_projBundleModelCochainComplex_X : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), (∀ n, CategoryTheory.Injective (I.X n)) → ∀ n, CategoryTheory.Injective ((Jcx R q N I).X n) := by
  first | (exact @GlobalTheory.EtC.Jcx_X_injective) | (exact GlobalTheory.EtC.Jcx_X_injective) | (intros; apply GlobalTheory.EtC.Jcx_X_injective  <;> assumption)
end
