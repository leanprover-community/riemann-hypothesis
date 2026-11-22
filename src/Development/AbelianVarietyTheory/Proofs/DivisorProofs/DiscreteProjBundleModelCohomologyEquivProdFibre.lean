module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteSpaceCocycleVanishingPosStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjBundleCochainPresheafIsSheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueCochainOnDiscProduct

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec

noncomputable section

namespace GlobalTheory.EtC.DiscCoch

theorem cotPre_isSheaf (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) :
    Presheaf.IsSheaf Scheme.etaleTopology.{0} (cotPre R q N I n) := GlobalTheory.T.projBundleCochainPresheaf_isSheaf R q N I n

theorem jsec_bij (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (n : ℤ) (U : Scheme.{0}) :
    Function.Bijective (fun c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n =>
      (Jsec c : Sec ((Jcx R q N I).X n) U)) := by
  have := isIso_toSheafify Scheme.etaleTopology.{0} (cotPre_isSheaf R q N I n)
  have h2 : IsIso ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)) := inferInstance
  exact ConcreteCategory.bijective_of_isIso ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U))

theorem glue (R : Type) [CommRing R] (q N : ℕ) (I : Cx R) (F : PSh) (n : ℤ)
    (c : ∀ U : Scheme.{0}, F.obj (op U) → Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n)
    (hc : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : F.obj (op U)), c V (F.map g.op x) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (c U x) (zero_add n)) :
    ∃! γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n, ∀ (U : Scheme.{0}) (x : F.obj (op U)),
      (Cochain.ofHom ((chains R).map (prod.map (disc.map (yonedaEquiv.symm x)) (𝟙 (fibQ q N))))).comp γ (zero_add n) =
        c U x := GlobalTheory.T.unique_cochain_on_disc_product R q N I F n c hc

variable {R : Type} [CommRing R] {q N : ℕ} {I : Cx R} {F : PSh}

theorem sec_map_at_zero {A B : Shv R} {U : Scheme.{0}} (φ : A ⟶ B) : Sec.map φ (0 : Sec A U) = 0 :=
  map_zero (φ.hom.app (op U)).hom

theorem jsec_res {n : ℤ} {V U : Scheme.{0}} (g : V ⟶ U) (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    Sec.res g (Jsec c) = Jsec ((Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp c (zero_add n)) :=
  (ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).naturality g.op) c).symm

theorem jsec_d {n m : ℤ} (hm : n + 1 = m) {U : Scheme.{0}} (c : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    Sec.map ((Jcx R q N I).d n m) (Jsec c) = Jsec (δ n m c) := by
  subst hm
  have h := ConcreteCategory.congr_hom (congrArg (fun φ => NatTrans.app φ (op U))
    (toSheafify_naturality Scheme.etaleTopology.{0} (cotD R q N I n))) c
  have hd : (Jcx R q N I).d n (n + 1) = (presheafToSheaf Scheme.etaleTopology.{0} _).map (cotD R q N I n) :=
    by simp only [Jcx, CochainComplex.of_d]
  rw [hd]
  exact h.symm

theorem jsec_add {n : ℤ} {U : Scheme.{0}} (a b : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) :
    (Jsec (a + b) : Sec ((Jcx R q N I).X n) U) = Jsec a + Jsec b :=
  map_add ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)).hom a b

theorem jsec_zero {n : ℤ} {U : Scheme.{0}} :
    (Jsec (0 : Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n) : Sec ((Jcx R q N I).X n) U) = 0 :=
  map_zero ((toSheafify Scheme.etaleTopology.{0} (cotPre R q N I n)).app (op U)).hom

def ptFst {U : Scheme.{0}} (x : F.obj (op U)) : sch.obj U ⟶ disc.obj F := disc.map (yonedaEquiv.symm x)

theorem ptFst_res {V U : Scheme.{0}} (g : V ⟶ U) (x : F.obj (op U)) : ptFst (F.map g.op x) = sch.map g ≫ ptFst x := by
  have e : yonedaEquiv.symm (F.map g.op x) = yoneda.map g ≫ yonedaEquiv.symm x := yonedaEquiv_symm_map g.op x
  show disc.map (yonedaEquiv.symm (F.map g.op x)) = disc.map (yoneda.map g) ≫ disc.map (yonedaEquiv.symm x)
  exact (congrArg disc.map e).trans (disc.map_comp _ _)

def ptMap {U : Scheme.{0}} (x : F.obj (op U)) : sch.obj U ⨯ fibQ q N ⟶ disc.obj F ⨯ fibQ q N :=
  prod.map (ptFst x) (𝟙 (fibQ q N))

def ptPull {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) {U : Scheme.{0}} (x : F.obj (op U)) :
    Cochain ((chains R).obj (sch.obj U ⨯ fibQ q N)) I n :=
  (Cochain.ofHom ((chains R).map (ptMap (q := q) (N := N) x))).comp γ (zero_add n)

theorem ptMap_res {V U : Scheme.{0}} (g : V ⟶ U) (x : F.obj (op U)) :
    (ptMap (F.map g.op x) : sch.obj V ⨯ fibQ q N ⟶ _) = prod.map (sch.map g) (𝟙 (fibQ q N)) ≫ ptMap x := by
  unfold ptMap
  rw [ptFst_res, prod.map_map, Category.comp_id]

theorem ptPull_res {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : F.obj (op U)) : ptPull γ (F.map g.op x) =
      (Cochain.ofHom ((chains R).map (prod.map (sch.map g) (𝟙 (fibQ q N))))).comp (ptPull γ x) (zero_add n) := by
  unfold ptPull
  rw [ptMap_res (q := q) (N := N), Functor.map_comp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem comp_δ {K L M : Cx R} {n m : ℤ} (hm : n + 1 = m) (f : K ⟶ L) (γ : Cochain L M n) :
    δ n m ((Cochain.ofHom f).comp γ (zero_add n)) = (Cochain.ofHom f).comp (δ n m γ) (zero_add m) := by
  rw [δ_zero_cochain_comp _ _ _ hm, δ_ofHom, Cochain.zero_comp, smul_zero, add_zero]

theorem ptPull_δ {n m : ℤ} (hm : n + 1 = m) (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n)
    {U : Scheme.{0}} (x : F.obj (op U)) : ptPull (δ n m γ) x = δ n m (ptPull γ x) :=
  (comp_δ hm _ γ).symm

theorem ptPull_add {n : ℤ} (a b : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) {U : Scheme.{0}}
    (x : F.obj (op U)) : ptPull (a + b) x = ptPull a x + ptPull b x := Cochain.comp_add _ _ _ _

theorem ptPull_zero {n : ℤ} {U : Scheme.{0}} (x : F.obj (op U)) :
    ptPull (0 : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) x = 0 := Cochain.comp_zero _ _

end GlobalTheory.EtC.DiscCoch

namespace GlobalTheory.EtC.DiscCoch

variable {R : Type} [CommRing R] {q N : ℕ} {I : Cx R} {F : PSh}

def aS {n : ℤ} (γ : Cochain ((chains R).obj (disc.obj F ⨯ fibQ q N)) I n) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx (disc.obj F) p U → Sec ((Jcx R q N I).X s) U
  | 0, s, h, U, x => (show n = s by simpa using h) ▸ Jsec (ptPull γ (show F.obj (op U) from x))
  | _ + 1, _, _, _, _ => 0

end GlobalTheory.EtC.DiscCoch
