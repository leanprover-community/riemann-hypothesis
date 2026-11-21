import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullAwChainsBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainProductAlexanderWhitneyFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvPullbackPgl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.PBFc
variable {R : Type} [CommRing R]
set_option backward.isDefEq.respectTransparency false in
theorem biChains_dh (X : SimplicialObject Spc) (a b : ℕ) :
    (biChainsXIso R X (a + 1) b).inv ≫ ((biChains R X).d (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ))).f (-(b : ℤ)) =
      (∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map ((X.δ i).app (op (SimplexCategory.mk b)))) ≫
        (biChainsXIso R X a b).inv := by
  let D := (dblF R).obj ((freeBi R).obj X)
  let M := ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj D
  have h1 : (biChains R X).d (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ)) =
      (M.extendXIso ComplexShape.embeddingDownNat (i := a + 1) rfl).hom ≫ M.d (a + 1) a ≫
        (M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv :=
    HomologicalComplex.extend_d_eq M ComplexShape.embeddingDownNat rfl rfl
  have h2 : ∀ p : ℕ, (biChainsXIso R X p b).inv =
      @CategoryStruct.comp _ _ _ ((M.X p).X (-(b : ℤ))) _
        ((D.X p).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).inv
        ((M.extendXIso ComplexShape.embeddingDownNat (i := p) rfl).inv.f (-(b : ℤ))) := fun p => rfl
  have h3 : (M.d (a + 1) a).f (-(b : ℤ)) = ((D.X (a+1)).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).hom ≫
      (D.d (a + 1) a).f b ≫ ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := b) rfl
  have key : (M.extendXIso ComplexShape.embeddingDownNat (i := a + 1) rfl).inv.f (-(b : ℤ)) ≫
      (M.extendXIso ComplexShape.embeddingDownNat (i := a + 1) rfl).hom.f (-(b : ℤ)) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  rw [h1, h2, h2, HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, reassoc_of% key, h3,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  congr 2
  rw [show D.d (a + 1) a = ∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) •
      (((SimplicialObject.whiskering _ _).obj (AlgebraicTopology.alternatingFaceMapComplex (Shv R))).obj ((freeBi R).obj X)).δ i
    from AlgebraicTopology.alternatingFaceMapComplex_obj_d _ a]
  rw [← HomologicalComplex.eval_map, Functor.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Functor.map_zsmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem biChains_dv (X : SimplicialObject Spc) (a b : ℕ) :
    (biChainsXIso R X a (b + 1)).inv ≫ ((biChains R X).X (-(a : ℤ))).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) =
      (∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • (free R).map ((X.obj (op (SimplexCategory.mk a))).δ j)) ≫
        (biChainsXIso R X a b).inv := by
  let D := (dblF R).obj ((freeBi R).obj X)
  let M := ((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj D
  have h2 : ∀ q : ℕ, (biChainsXIso R X a q).inv =
      @CategoryStruct.comp _ _ _ ((M.X a).X (-(q : ℤ))) _
        ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := q) rfl).inv
        ((M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv.f (-(q : ℤ))) := fun q => rfl
  have h3 : (M.X a).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) =
      ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := b + 1) rfl).hom ≫ (D.X a).d (b + 1) b ≫
        ((D.X a).extendXIso ComplexShape.embeddingDownNat (i := b) rfl).inv :=
    HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat rfl rfl
  have hc : (M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv.f (-((b + 1 : ℕ) : ℤ)) ≫
      ((biChains R X).X (-(a : ℤ))).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) =
      (M.X a).d (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) ≫ (M.extendXIso ComplexShape.embeddingDownNat (i := a) rfl).inv.f (-(b : ℤ)) :=
    HomologicalComplex.Hom.comm _ _ _
  rw [h2, h2, Category.assoc, hc, h3, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
  simp only [← Category.assoc]
  congr 2
  rw [show (D.X a).d (b + 1) b = ∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • ((freeBi R).obj X |>.obj (op (SimplexCategory.mk a))).δ j
    from AlgebraicTopology.alternatingFaceMapComplex_obj_d _ b]
  rfl

section Faces
variable {X : SimplicialObject Spc}

def BSx.hface {a b : ℕ} {U : Scheme.{0}} (y : BSx X (a + 1) b U) (i : Fin (a + 2)) : BSx X a b U :=
  ((X.δ i).app (op (SimplexCategory.mk b))).app (op U) y

def BSx.vface {a b : ℕ} {U : Scheme.{0}} (y : BSx X a (b + 1) U) (j : Fin (b + 2)) : BSx X a b U :=
  ((X.obj (op (SimplexCategory.mk a))).δ j).app (op U) y

variable {K : Cx R} {k : ℤ}

def evD (γ : Cochain (totChains R X) K k) (t : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx X a b U) : Sec (K.X t) U :=
  if h : -((a + b : ℕ) : ℤ) + k = t then evT γ a b t h U y else 0

theorem evD_eq (γ : Cochain (totChains R X) K k) (t : ℤ) (a b : ℕ) (h : -((a + b : ℕ) : ℤ) + k = t) (U : Scheme.{0})
    (y : BSx X a b U) : evD γ t a b U y = evT γ a b t h U y := dif_pos h

def hB (γ : Cochain (totChains R X) K k) (t : ℤ) : ∀ (a b : ℕ) (U : Scheme.{0}), BSx X a b U → Sec (K.X t) U
  | 0, _, _, _ => 0
  | a + 1, b, U, y => ∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • evD γ t a b U (y.hface i)

def vB (γ : Cochain (totChains R X) K k) (t : ℤ) : ∀ (a b : ℕ) (U : Scheme.{0}), BSx X a b U → Sec (K.X t) U
  | _, 0, _, _ => 0
  | a, b + 1, U, y => ∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • evD γ t a b U (y.vface j)

end Faces

theorem ιTotal_v_congr {X : SimplicialObject Spc} {K : Cx R} {k : ℤ} (γ : Cochain (totChains R X) K k) (i₁ i₂ p p' t : ℤ)
    (hp : p = p') (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⟨i₁, i₂⟩ = p)
    (h' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⟨i₁, i₂⟩ = p')
    (hv : p + k = t) (hv' : p' + k = t) :
    (biChains R X).ιTotal (ComplexShape.up ℤ) i₁ i₂ p h ≫ γ.v p t hv =
      (biChains R X).ιTotal (ComplexShape.up ℤ) i₁ i₂ p' h' ≫ γ.v p' t hv' := by
  subst hp
  rfl

theorem evT_dh {X : SimplicialObject Spc} {K : Cx R} {k : ℤ} (γ : Cochain (totChains R X) K k) (a b : ℕ) (p t : ℤ)
    (hp : -((a + b : ℕ) : ℤ) + 1 = p) (hv : p + k = t) (U : Scheme.{0}) (y : BSx X a b U) :
    Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).d₁ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) p ≫ γ.v p t hv)
      (freeGen R _ U y) = hB γ t a b U y := by
  cases a with
  | zero =>
    rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℤ).Rel (-((0 : ℕ) : ℤ)) 1 from by simp) (-(b : ℤ)) p
      (by simp only [ComplexShape.π_def]; omega),
      (biChains_isZero X 1 (-(b : ℤ)) (Or.inl one_pos)).eq_of_tgt (HomologicalComplex.Hom.f _ _) 0]
    simp only [zero_comp, smul_zero, comp_zero]
    exact map_zero (mapHom _ _ (freeGen R _ U y))
  | succ a =>
    rw [HomologicalComplex₂.d₁_eq _ _ (show (ComplexShape.up ℤ).Rel (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ)) from by simp <;> omega)
      (-(b : ℤ)) p (by simp only [ComplexShape.π_def]; omega)]
    show _ = ∑ i : Fin (a + 2), (-1 : ℤ) ^ (i : ℕ) • evD γ t a b U (y.hface i)
    rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (-((a + 1 : ℕ) : ℤ), -(b : ℤ)) = 1 from rfl,
      one_smul, Category.assoc, ← Category.assoc _ (HomologicalComplex.Hom.f _ _), biChains_dh, Category.assoc,
      Preadditive.sum_comp]
    refine (map_sum (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map (_ ≫ _ ≫ γ.v p t hv) (Sec.map ((free R).map _) (freeGen R _ U y)) = _
    rw [freeGen_map, evD_eq γ t a b (by omega)]
    unfold evT
    rw [ιTotal_v_congr γ _ _ p (-((a + b : ℕ) : ℤ)) t (by omega) _ (by simp only [ComplexShape.π_def]; omega) hv]
    rfl

theorem evT_dv {X : SimplicialObject Spc} {K : Cx R} {k : ℤ} (γ : Cochain (totChains R X) K k) (a b : ℕ) (p t : ℤ)
    (hp : -((a + b : ℕ) : ℤ) + 1 = p) (hv : p + k = t) (U : Scheme.{0}) (y : BSx X a b U) :
    Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).d₂ (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ)) p ≫ γ.v p t hv)
      (freeGen R _ U y) = (a : ℤ).negOnePow • vB γ t a b U y := by
  cases b with
  | zero =>
    rw [HomologicalComplex₂.d₂_eq _ _ _ (show (ComplexShape.up ℤ).Rel (-((0 : ℕ) : ℤ)) 1 from by simp) p
      (by simp only [ComplexShape.π_def]; omega),
      (biChains_isZero X (-(a : ℤ)) 1 (Or.inr one_pos)).eq_of_tgt (HomologicalComplex.d _ _ _) 0]
    simp only [zero_comp, smul_zero, comp_zero]
    exact (map_zero (mapHom _ _ (freeGen R _ U y))).trans (smul_zero _).symm
  | succ b =>
    show _ = (a : ℤ).negOnePow • ∑ j : Fin (b + 2), (-1 : ℤ) ^ (j : ℕ) • evD γ t a b U (y.vface j)
    rw [HomologicalComplex₂.d₂_eq _ _ _ (show (ComplexShape.up ℤ).Rel (-((b + 1 : ℕ) : ℤ)) (-(b : ℤ)) from by simp <;> omega)
      p (by simp only [ComplexShape.π_def]; omega),
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (-(a : ℤ), -((b + 1 : ℕ) : ℤ)) = (a : ℤ).negOnePow
        by simp,
      Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    refine (map_zsmul (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans ?_
    rw [Units.smul_def]
    congr 1
    rw [Category.assoc, ← Category.assoc _ (HomologicalComplex.d _ _ _), biChains_dv, Category.assoc, Preadditive.sum_comp]
    refine (map_sum (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map (_ ≫ _ ≫ γ.v p t hv) (Sec.map ((free R).map _) (freeGen R _ U y)) = _
    rw [freeGen_map, evD_eq γ t a b (by omega)]
    unfold evT
    rw [ιTotal_v_congr γ _ _ p (-((a + b : ℕ) : ℤ)) t (by omega) _ (by simp only [ComplexShape.π_def]; omega) hv]
    rfl

theorem evT_δ {X : SimplicialObject Spc} {K : Cx R} {k k' : ℤ} (hk : k + 1 = k') (γ : Cochain (totChains R X) K k)
    (a b : ℕ) (s t : ℤ) (hs : -((a + b : ℕ) : ℤ) + k = s) (ht : -((a + b : ℕ) : ℤ) + k' = t) (U : Scheme.{0})
    (y : BSx X a b U) :
    evT (δ k k' γ) a b t ht U y = Sec.map (K.d s t) (evT γ a b s hs U y) +
      k'.negOnePow • (hB γ t a b U y + (a : ℤ).negOnePow • vB γ t a b U y) := by
  rw [evT, δ_v k k' hk γ _ t ht s (-((a + b : ℕ) : ℤ) + 1) (by omega) rfl, Preadditive.comp_add, Preadditive.comp_add]
  refine (map_add (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (congrArg₂ (· + ·) ?_ ?_)
  · simp only [← Category.assoc]
    rfl
  · rw [Units.smul_def, Preadditive.comp_zsmul, Preadditive.comp_zsmul]
    refine (map_zsmul (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans ?_
    rw [Units.smul_def]
    congr 1
    rw [HomologicalComplex₂.total_d, Preadditive.add_comp, Preadditive.comp_add, ← Category.assoc, HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂_assoc, Preadditive.comp_add]
    refine (map_add (mapHom _ (K.X t) (freeGen R _ U y)) _ _).trans (congrArg₂ (· + ·) ?_ ?_)
    · exact evT_dh γ a b _ t rfl _ U y
    · exact evT_dv γ a b _ t rfl _ U y

section Cross2
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

theorem vertS_hface {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) (a + 1) b U) (i : Fin (a + 2)) :
    vertS V ℓ (y.hface i) = vertS V ℓ y := by
  have h := ℓ.naturality (SimplexCategory.δ i).op
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (NatTrans.congr_app h (op (SimplexCategory.mk b))) (op U)) y

theorem vertS_vface {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a (b + 1) U) (j : Fin (b + 2)) :
    vertS V ℓ (y.vface j) = (vertS V ℓ y).face j :=
  ConcreteCategory.congr_hom (NatTrans.congr_app ((ℓ.app (op (SimplexCategory.mk a))).naturality
    (SimplexCategory.δ j).op) (op U)) y

end Cross2

section Two
variable {E B : Spc} {U : Scheme.{0}} {I J K : Cx R} (μ : Pair I J K) {n m : ℤ}

def bisimplexFunctionBoundaryFirst {A : Type*} [AddCommGroup A] (φ : ∀ p r : ℕ, Sx E p U → Sx B r U → A) : ∀ p r : ℕ, Sx E p U → Sx B r U → A
  | 0, _, _, _ => 0
  | p + 1, r, x, v => ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • φ p r (x.face i) v

def bisimplexFunctionBoundarySecond {A : Type*} [AddCommGroup A] (φ : ∀ p r : ℕ, Sx E p U → Sx B r U → A) : ∀ p r : ℕ, Sx E p U → Sx B r U → A
  | _, 0, _, _ => 0
  | p, r + 1, x, v => ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) • φ p r x (v.face j)

def xv (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (w : ℤ) (p r : ℕ) (x : Sx E p U)
    (v : Sx B r U) : Sec (K.X w) U :=
  if h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = w then μ.mul U _ _ w h (ev α p _ rfl U x) (ev z r _ rfl U v) else 0

theorem xv_eq (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (w : ℤ) (p r : ℕ) (x : Sx E p U)
    (v : Sx B r U) (s t : ℤ) (hs : -(p : ℤ) + n = s) (ht : -(r : ℤ) + m = t) (h : s + t = w) :
    xv μ α z w p r x v = μ.mul U s t w h (ev α p s hs U x) (ev z r t ht U v) := by
  subst hs ht
  exact dif_pos h

theorem xv_δ_left {n₁ : ℤ} (hn : n + 1 = n₁) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m)
    (w : ℤ) (p r : ℕ) (x : Sx E p U) (v : Sx B r U) (s s' t : ℤ) (hs : -(p : ℤ) + n = s) (hs' : s + 1 = s')
    (ht : -(r : ℤ) + m = t) (h : s' + t = w) :
    μ.mul U s' t w h (Sec.map (I.d s s') (ev α p s hs U x)) (ev z r t ht U v) =
      xv μ (δ n n₁ α) z w p r x v - sg n₁ • bisimplexFunctionBoundaryFirst (xv μ α z w) p r x v := by
  rw [xv_eq μ _ z w p r x v s' t (by omega) ht h]
  cases p with
  | zero => rw [ev_δ_zero hn α U s s' hs, bisimplexFunctionBoundaryFirst, smul_zero, sub_zero]
  | succ p =>
    rw [ev_δ_succ hn α U p s s' hs, bisimplexFunctionBoundaryFirst, map_add, LinearMap.add_apply, sg_smul, map_zsmul, LinearMap.smul_apply, map_sum,
      LinearMap.sum_apply, eq_sub_iff_add_eq]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_zsmul, LinearMap.smul_apply, xv_eq μ α z w p r _ v s' t (by omega) ht h]

theorem xv_δ_right {m₁ : ℤ} (hm : m + 1 = m₁) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m)
    (w : ℤ) (p r : ℕ) (x : Sx E p U) (v : Sx B r U) (s t t' : ℤ) (hs : -(p : ℤ) + n = s)
    (ht : -(r : ℤ) + m = t) (ht' : t + 1 = t') (h : s + t' = w) :
    μ.mul U s t' w h (ev α p s hs U x) (Sec.map (J.d t t') (ev z r t ht U v)) =
      xv μ α (δ m m₁ z) w p r x v - sg m₁ • bisimplexFunctionBoundarySecond (xv μ α z w) p r x v := by
  rw [xv_eq μ α _ w p r x v s t' hs (by omega) h]
  cases r with
  | zero => rw [ev_δ_zero hm z U t t' ht, bisimplexFunctionBoundarySecond, smul_zero, sub_zero]
  | succ r =>
    rw [ev_δ_succ hm z U r t t' ht, bisimplexFunctionBoundarySecond, map_add, sg_smul, map_zsmul, map_sum, eq_sub_iff_add_eq]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_zsmul, xv_eq μ α z w p r x _ s t' hs (by omega) h]

theorem d_xv {n₁ m₁ : ℤ} (hn : n + 1 = n₁) (hm : m + 1 = m₁) (α : Cochain ((chains R).obj E) I n)
    (z : Cochain ((chains R).obj B) J m) (w w' : ℤ) (hw : w + 1 = w') (p r : ℕ) (x : Sx E p U) (v : Sx B r U)
    (h : (-(p : ℤ) + n) + (-(r : ℤ) + m) = w) :
    Sec.map (K.d w w') (xv μ α z w p r x v) =
      (xv μ (δ n n₁ α) z w' p r x v - sg n₁ • bisimplexFunctionBoundaryFirst (xv μ α z w') p r x v) +
        sg (-(p : ℤ) + n) • (xv μ α (δ m m₁ z) w' p r x v - sg m₁ • bisimplexFunctionBoundarySecond (xv μ α z w') p r x v) := by
  subst hw
  rw [xv_eq μ α z w p r x v _ _ rfl rfl h, μ.leibniz, xv_δ_left μ hn α z _ p r x v _ _ _ rfl rfl rfl,
    xv_δ_right μ hm α z _ p r x v _ _ _ rfl rfl rfl, sg_smul]

end Two

theorem evT_usmul {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (c : ℤˣ) (γ : Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (c • γ) a b s h U y = c • evT γ a b s h U y := by
  unfold evT
  rw [Units.smul_def, Units.smul_def, Cochain.smul_v, Preadditive.comp_zsmul, Preadditive.comp_zsmul]
  exact map_zsmul (mapHom _ _ (freeGen R _ U y)) _ _

section Cross3
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)
  {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n)
  (z : Cochain ((chains R).obj B) J m)

theorem evT_crossT_xv (a b : ℕ) (w : ℤ) (h : -((a + b : ℕ) : ℤ) + k = w) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    evT (crossT V ℓ μ hk α z) a b w h U y = sg (m * a) • xv μ α z w a b (baseS V y) (vertS V ℓ y) := by
  rw [evT_crossT, xv_eq μ α z w a b _ _ _ _ rfl rfl (by push_cast at h; omega), sg_smul]

theorem evD_crossT (w : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    evD (crossT V ℓ μ hk α z) w a b U y = sg (m * a) • xv μ α z w a b (baseS V y) (vertS V ℓ y) := by
  by_cases h : -((a + b : ℕ) : ℤ) + k = w
  · rw [evD_eq _ _ _ _ h, evT_crossT_xv]
  · rw [evD, dif_neg h, xv, dif_neg (by push_cast at h; omega), smul_zero]

theorem hB_crossT (w : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    hB (crossT V ℓ μ hk α z) w a b U y = sg (m * a + m) • bisimplexFunctionBoundaryFirst (xv μ α z w) a b (baseS V y) (vertS V ℓ y) := by
  cases a with
  | zero => rw [hB, bisimplexFunctionBoundaryFirst, smul_zero]
  | succ a =>
    rw [hB, bisimplexFunctionBoundaryFirst, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evD_crossT, vertS_hface, smul_comm]
    congr 1
    rw [show m * ((a + 1 : ℕ) : ℤ) + m = m * a + (m + m) by push_cast; ring, sg_add, sg_add, sg_sq, mul_one]

theorem vB_crossT (w : ℤ) (a b : ℕ) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    vB (crossT V ℓ μ hk α z) w a b U y = sg (m * a) • bisimplexFunctionBoundarySecond (xv μ α z w) a b (baseS V y) (vertS V ℓ y) := by
  cases b with
  | zero => rw [vB, bisimplexFunctionBoundarySecond, smul_zero]
  | succ b =>
    rw [vB, bisimplexFunctionBoundarySecond, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evD_crossT, vertS_vface, smul_comm]
    rfl

end Cross3

theorem crossT_leibniz {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k n' m' k' : ℤ}
    (hk : n + m = k) (hn : n + 1 = n') (hm : m + 1 = m') (hk' : k + 1 = k') (hk₁ : n' + m = k') (hk₂ : n + m' = k')
    (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) :
    δ k k' (crossT V ℓ μ hk α z) = crossT V ℓ μ hk₁ (δ n n' α) z + n.negOnePow • crossT V ℓ μ hk₂ α (δ m m' z) := by
  refine evT_ext _ _ fun a b t ht U y => ?_
  rw [evT_add, evT_usmul, evT_δ hk' _ a b (-((a + b : ℕ) : ℤ) + k) t rfl ht U y, evT_crossT_xv, evT_crossT_xv,
    evT_crossT_xv, hB_crossT, vB_crossT]
  have hd := d_xv μ hn hm α z (-((a + b : ℕ) : ℤ) + k) t (by omega) a b (baseS V y) (vertS V ℓ y) (by push_cast; omega)
  rw [Sec.map] at hd
  rw [Sec.map, map_zsmul, hd]
  clear hd
  subst hn hm hk hk'
  have e1 : sg ((m + 1) * (a : ℤ)) = sg (m * a) * sg a := by rw [add_mul, one_mul, sg_add]
  rw [e1]
  simp only [sg_smul, sg_add, sg_neg, sg_one]
  have q1 := sg_sq m
  have q2 := sg_sq n
  have q3 := sg_sq (a : ℤ)
  have q4 := sg_sq (m * (a : ℤ))
  generalize sg m = σm at *
  generalize sg n = σn at *
  generalize sg (a : ℤ) = σa at *
  generalize sg (m * (a : ℤ)) = σ at *
  match_scalars <;> first | ring1 | linear_combination (-(σ * σn)) * q1 | linear_combination (σ * σn) * q1

end GlobalTheory.PBFc

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crossProductTwisted_leibniz_rule : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k n' m' k' : ℤ} (hk : n + m = k) (hn : n + 1 = n') (hm : m + 1 = m') (hk' : k + 1 = k') (hk₁ : n' + m = k') (hk₂ : n + m' = k') (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m), δ k k' (crossT V ℓ μ hk α z) = crossT V ℓ μ hk₁ (δ n n' α) z + n.negOnePow • crossT V ℓ μ hk₂ α (δ m m' z) := by
  first | (exact @GlobalTheory.PBFc.crossT_leibniz) | (exact GlobalTheory.PBFc.crossT_leibniz) | (intros; apply GlobalTheory.PBFc.crossT_leibniz  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFc

theorem crossT_ι_eq_zero_of_vanish {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ}
    (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (p : ℤ)
    (hα : ∀ c r hr, p < c → α.v c r hr = 0) (c l t : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + k = r)
    (hc : p < c) :
    (biChains R (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (crossT V ℓ μ hk α z).v t r hr = 0 := by
  have ht : c + l = t := h
  by_cases hcl : c ≤ 0 ∧ l ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
    obtain rfl : t = -((a + b : ℕ) : ℤ) := by push_cast; omega
    rw [← cancel_epi (biChainsXIso R (twX E V) a b).inv, comp_zero]
    refine free_ext _ _ fun U y => ?_
    have e1 := evT_crossT V ℓ μ hk α z a b r hr U y
    unfold evT at e1
    refine e1.trans ?_
    have h0 : ev α a _ rfl U (baseS V y) = 0 := by
      rw [ev_def, hα _ _ _ hc, comp_zero]
      exact map_zero (mapHom _ _ (freeGen R _ U (baseS V y)))
    rw [h0, map_zero, LinearMap.zero_apply, smul_zero]
    exact (map_zero (mapHom _ _ (freeGen R _ U y))).symm
  · exact (biChains_isZero (R := R) (twX E V) c l (by omega)).eq_of_src _ _

end GlobalTheory.PBFc
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_product_vanishing_above_degree : ∀ {R : Type} [CommRing R] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (z : Cochain ((chains R).obj B) J m) (p : ℤ) (hα : ∀ c r hr, p < c → α.v c r hr = 0) (c l t : ℤ) (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + k = r) (hc : p < c), (biChains R (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (crossT V ℓ μ hk α z).v t r hr = 0 := by
  first | (exact @GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish) | (exact GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish) | (intros; apply GlobalTheory.PBFc.crossT_ι_eq_zero_of_vanish  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section
namespace GlobalTheory.PBFc

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ n' (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ n x) := by
  subst hn; subst hi; rfl

theorem cast_cup (q : ℕ) {E : Spc} {n m k a b c : ℤ} (hk : n + m = k) (hc : a + b = c) (x : Ht q E n a) (y : Ht q E m b) :
    Ht.cast hk hc ((twPair q a b).cup E rfl x y) =
      (Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q a)) (res (ZMod q) (tw q b)) (res (ZMod q) (tw q k)))
        (twPair q a b) hc).cup E hk x y := by
  subst hk; subst hc; rfl

theorem cls_term (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ) (j : Fin N)
    (z : Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hz : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) z (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (a : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res _ (tw q i)) n,
      γ.1 = (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp
        (crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1) (zero_add n) ∧
      pull _ (twIso E V).hom _ n (Ht.cast (by ring) (by ring) (cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (CohomologyClass.mk a))
        (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) : Ht q _ n i) = CohomologyClass.mk γ := by
  set c := (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp
    (crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1) (zero_add n) with hcdef
  have hAW := GlobalTheory.T.cochain_product_alexander_whitney_formula V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) a.1 z.1 c (fun M s h => by
    rw [hcdef, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, awChains_f])
  have hδ := aw_cocycle (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _)
    (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (twPi E V))) a (zero_add _))
    (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) z (zero_add _)) c (by
      simpa only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe] using hAW)
  refine ⟨Cocycle.mk c (n + 1) rfl hδ, rfl, ?_⟩
  rw [pull_cast]
  change Ht.cast _ _ (cpull ((chains (ZMod q)).map (twIso E V).hom) _ _ ((twPair q _ _).cup _ rfl _ _)) = _
  rw [Pair.cup_pull, cast_cup]
  change (twPairI q i ((j : ℕ) : ℤ)).cup _ _ (pull _ (twIso E V).hom _ _ (pull _ (pullback.fst V (PGL.pr N)) _ _ (CohomologyClass.mk a)))
    (pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) = _
  rw [← pull_comp, twIso_hom_fst, ← hz]
  refine Pair.cup_spec _ _ _ (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (twPi E V))) a (zero_add _)) _ _ ?_
  simpa only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe] using hAW

theorem pbfMap_eq_cpull_aw (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ)
    (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hz : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n)
    (hb : b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1)) :
    pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) =
      cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n (CohomologyClass.mk b) := by
  choose γ hγ hγc using fun j : Fin N => cls_term q V ℓ n i j (z j) (hz j) (a j)
  have e1 : pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) =
      ∑ j : Fin N, CohomologyClass.mk (γ j) := by
    unfold pbfMap
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hγc j
  have e2 : zcomp (Cocycle.ofHom (awChains (ZMod q) (twX E V))) b (zero_add n) = ∑ j : Fin N, γ j := by
    apply Cocycle.ext
    have hs := map_sum (AddSubgroup.subtype (cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res (ZMod q) (tw q i)) n)) γ Finset.univ
    refine Eq.trans ?_ hs.symm
    change _ = ∑ j, (γ j).1
    simp only [hγ]
    change (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp b.1 (zero_add n) = _
    rw [hb, phi_apply]
    exact map_sum (AddMonoidHom.mk' (fun x : Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n =>
      (Cochain.ofHom (awChains (ZMod q) (twX E V))).comp x (zero_add n)) (fun x y => Cochain.comp_add _ _ _ _)) _ _
  rw [e1, cpre_mk, e2]
  exact (map_sum (AddMonoidHom.mk' (CohomologyClass.mk : Cocycle ((chains (ZMod q)).obj (bidiag.obj (twX E V))) (res _ (tw q i)) n → _)
    (fun x y => CohomologyClass.mk_add x y)) _ _).symm

end GlobalTheory.PBFc
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_cocycle_classes_pullback_cup : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (n i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) = pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ))) (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n) (hb : b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1)), pull _ (twIso E V).hom _ n (pbfMap q V n i (fun j => CohomologyClass.mk (a j))) = cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n (CohomologyClass.mk b) := by
  first | (exact @GlobalTheory.PBFc.pbfMap_eq_cpull_aw) | (exact GlobalTheory.PBFc.pbfMap_eq_cpull_aw) | (intros; apply GlobalTheory.PBFc.pbfMap_eq_cpull_aw  <;> assumption)
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFg
variable (R : Type) [CommRing R]
open GlobalTheory.EtC.DiscChains

def colCx (X : SimplicialObject Spc) (a : ℕ) :
    (biChains R X).X (-(a : ℤ)) ≅ (chains R).obj (X.obj (op (SimplexCategory.mk a))) :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) rfl ≪≫
    (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapIso (Iso.refl _)

theorem colCx_f (X : SimplicialObject Spc) (a b : ℕ) :
    (biChainsXIso R X a b).inv ≫ (colCx R X a).hom.f (-(b : ℤ)) =
      (chainsXIso R (X.obj (op (SimplexCategory.mk a))) b).inv := by
  have h1 := (HomologicalComplex.extendXIso (((ComplexShape.embeddingDownNat.extendFunctor (Shv R)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj ((dblF R).obj ((freeBi R).obj X))) ComplexShape.embeddingDownNat (i := a) (i' := -(a:ℤ)) rfl).inv_hom_id
  have h2 := congrArg (fun f => HomologicalComplex.Hom.f f (-(b:ℤ))) h1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at h2
  erw [Iso.trans_hom, HomologicalComplex.comp_f, Iso.trans_inv]
  erw [Category.assoc, reassoc_of% h2]
  erw [Functor.mapIso_refl, Iso.refl_hom, HomologicalComplex.id_f, Category.comp_id]
  rfl

def prE (E : Spc) (a : ℕ) : (chains R).obj (disc.obj (E.obj (op (SimplexCategory.mk a)))) ⟶
    sgl (((chains R).obj E).X (-(a : ℤ))) :=
  (he R _).inv ≫ (CochainComplex.singleFunctor (Shv R) 0).map (chainsXIso R E a).inv

def prEquiv (E : Spc) (a : ℕ) : HomotopyEquiv ((chains R).obj (disc.obj (E.obj (op (SimplexCategory.mk a)))))
    (sgl (((chains R).obj E).X (-(a : ℤ)))) :=
  (he R _).symm.trans (HomotopyEquiv.ofIso ((CochainComplex.singleFunctor (Shv R) 0).mapIso (chainsXIso R E a).symm))

theorem prE_zero (E : Spc) (a : ℕ) :
    (chainsXIso R (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0).inv ≫ (prE R E a).f 0 =
      (chainsXIso R E a).inv ≫ sglι _ := by
  set P := E.obj (op (SimplexCategory.mk a))
  have hφψ : (he R P).hom.f 0 ≫ (he R P).inv.f 0 = 𝟙 _ := by
    have hc := (he R P).homotopyHomInvId.comm 0
    have hz1 : IsZero ((sgl ((free R).obj P)).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)
    have hzm : IsZero ((sgl ((free R).obj P)).X (-1)) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide)
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp), prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
      hz1.eq_of_tgt ((sgl ((free R).obj P)).d 0 1) 0, hzm.eq_of_tgt ((he R P).homotopyHomInvId.hom 0 (-1)) 0] at hc
    simp at hc
    exact hc
  have hinv0 : (chainsXIso R (disc.obj P) 0).inv ≫ (he R P).inv.f 0 = sglι ((free R).obj P) := by
    rw [← he_hom_f_zero R P, Category.assoc, hφψ, Category.comp_id]
  have h1 : sglι ((free R).obj P) ≫ ((CochainComplex.singleFunctor (Shv R) 0).map (chainsXIso R E a).inv).f 0 =
      (chainsXIso R E a).inv ≫ sglι _ := by
    change _ ≫ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map (chainsXIso R E a).inv).f 0 = _
    rw [HomologicalComplex.single_map_f_self]
    erw [Iso.inv_hom_id_assoc]
  rw [prE, HomologicalComplex.comp_f, ← Category.assoc, hinv0, h1]

theorem mk_sum_cocycle {K L : Cx R} {n : ℤ} {ι : Type} [DecidableEq ι] (s : Finset ι) (γ : ι → Cocycle K L n) :
    ∑ j ∈ s, CohomologyClass.mk (γ j) = CohomologyClass.mk (∑ j ∈ s, γ j) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact (CohomologyClass.mk_zero (K := K) (L := L) (n := n)).symm
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ih, CohomologyClass.mk_add]

theorem pull_colIso_pbfMap (q : ℕ) [NeZero q] (P : PSh) {N : ℕ} (V₀ : disc.obj P ⟶ ofCat (glCat N))
    (hP : Inv q (disc.obj P)) (m i : ℤ) (x : ∀ j : Fin N, Ht q (disc.obj P) (m - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ (colIso P V₀).hom _ m (pbfMap q V₀ m i x) =
      ∑ j : Fin N, ((cup q (pull _ (ptimes.fst P (Fib N)) _ _ (x j))
        (cpow q (c1 q (ptimes.snd P (Fib N) ≫ Fib.line N)) j)).cast (by ring) (by ring) : Ht q (ptimes P (Fib N)) m i) := by
  unfold pbfMap
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_htCast, (a6nat_holds q).1, ← pull_comp, colIso_hom_fst, pull_cpow q a6nat_holds _ (inv_pullback_pgl q V₀ hP),
    (a6nat_holds q).2.2.1 _ _ (inv_pullback_pgl q V₀ hP), colIso_line]

theorem ev_prE_pos (E : Spc) (a : ℕ) {I : Cx R} {d : ℤ} (c : Cochain (sgl (((chains R).obj E).X (-(a : ℤ)))) I d)
    (s : ℕ) (t : ℤ) (h : -(s : ℤ) + d = t) (U : Scheme.{0})
    (x : Sx (disc.obj (E.obj (op (SimplexCategory.mk a)))) s U) (hs : 0 < s) :
    ev ((Cochain.ofHom (prE R E a)).comp c (zero_add d)) s t h U x = 0 := by
  have hz : IsZero ((sgl (((chains R).obj E).X (-(a : ℤ)))).X (-(s : ℤ))) :=
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ (-(s : ℤ)) (by omega)
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, hz.eq_of_src (c.v (-(s : ℤ)) t h) 0, comp_zero, comp_zero]
  exact map_zero (mapHom _ _ (freeGen R _ U x))

theorem ev_prE_zero (E : Spc) (a : ℕ) {I : Cx R} {d : ℤ} (c : Cochain (sgl (((chains R).obj E).X (-(a : ℤ)))) I d)
    (t : ℤ) (h : -((0 : ℕ) : ℤ) + d = t) (U : Scheme.{0}) (x : Sx (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0 U) :
    ev ((Cochain.ofHom (prE R E a)).comp c (zero_add d)) 0 t h U x =
      Sec.map ((chainsXIso R E a).inv ≫ sglι _ ≫ c.v 0 t (by simpa using h)) (freeGen R _ U x) := by
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  change Sec.map ((chainsXIso R (disc.obj (E.obj (op (SimplexCategory.mk a)))) 0).inv ≫ (prE R E a).f 0 ≫ c.v 0 t _) _ = _
  rw [reassoc_of% prE_zero R E a]
  rfl

end GlobalTheory.PBFg
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFc

theorem cup_cast_mk_of_isAW_rec (q : ℕ) {S : Spc} (a b k n m N : ℤ) (e : a + b = k) (hN : n + m = N)
    (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q a)) n)
    (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q b)) m)
    (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q k)) N)
    (h : (Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q a)) (res (ZMod q) (tw q b)) (res (ZMod q) (tw q k)))
      (twPair q a b) e).IsAW hN α.1 β.1 γ.1) :
    ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast hN e : Ht q S N k) = CohomologyClass.mk γ := by
  subst e
  subst hN
  exact Pair.cup_spec (twPair q a b) S rfl α β γ h

theorem cup_cast_mk_of_isAW : ∀ (q : ℕ) {S : Spc} (i : ℤ) (j : ℕ) (m : ℤ) (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (i - (j : ℤ)))) (m - 2 * (j : ℤ))) (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (j : ℤ))) (2 * (j : ℤ))) (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q i)) m), (twPairI q i (j : ℤ)).IsAW (sub_add_cancel m _) α.1 β.1 γ.1 → ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast (by ring) (by ring) : Ht q S m i) = CohomologyClass.mk γ := by
  intro q S i j m α β γ h
  exact cup_cast_mk_of_isAW_rec q (i - (j : ℤ)) (j : ℤ) i (m - 2 * (j : ℤ)) (2 * (j : ℤ)) m
    (sub_add_cancel i _) (sub_add_cancel m _) α β γ h

end GlobalTheory.PBFc
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_cast_mk_of_isAlexanderWhitney : ∀ (q : ℕ) {S : Spc} (i : ℤ) (j : ℕ) (m : ℤ) (α : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (i - (j : ℤ)))) (m - 2 * (j : ℤ))) (β : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q (j : ℤ))) (2 * (j : ℤ))) (γ : Cocycle ((chains (ZMod q)).obj S) (res _ (tw q i)) m), (twPairI q i (j : ℤ)).IsAW (sub_add_cancel m _) α.1 β.1 γ.1 → ((cup q (CohomologyClass.mk α) (CohomologyClass.mk β)).cast (by ring) (by ring) : Ht q S m i) = CohomologyClass.mk γ := by
  first | (exact @GlobalTheory.PBFc.cup_cast_mk_of_isAW) | (exact GlobalTheory.PBFc.cup_cast_mk_of_isAW) | (intros; apply GlobalTheory.PBFc.cup_cast_mk_of_isAW  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.AWFront

theorem sub_full {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have e : SimplexCategory.subinterval (n := N) 0 N h = 𝟙 _ := by
    ext i
    simp [SimplexCategory.subinterval]
  unfold Sx.sub
  rw [e, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem ev_of_front {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {S : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj S) I n) (β : Cochain ((chains R).obj S) J m) (γ : Cochain ((chains R).obj S) K k)
    (hγ : μ.IsAW hk α β γ)
    (hα : ∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S s U), 0 < s → ev α s t h U x = 0)
    (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx S N U) :
    ev γ N w h U x = μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega)))
      (ev β N _ rfl U x) := by
  have key : ∀ (s : ℤ) (hs : s = n) (H : s + (-(N : ℤ) + m) = w) (h1 : -((0 : ℕ) : ℤ) + n = s),
      μ.mul U s (-(N : ℤ) + m) w H (ev α 0 s h1 U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) =
        μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
    rintro s rfl H h1
    rfl
  have gen : ∀ (p : ℕ), p = 0 → ∀ (H : -(p : ℤ) + n + (-((N - p : ℕ) : ℤ) + m) = w) (h1 : 0 + p ≤ N)
      (h2 : p + (N - p) ≤ N),
      (m * (p : ℤ)).negOnePow • μ.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w H
        (ev α p _ rfl U (x.sub 0 p h1)) (ev β (N - p) _ rfl U (x.sub p (N - p) h2)) =
      μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
    rintro p rfl H h1 h2
    have e1 : (m * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
    rw [e1, one_smul]
    have e2 : x.sub 0 (N - 0) h2 = x := sub_full x h2
    rw [e2]
    exact key _ (by simp) H rfl
  rw [hγ N w h U x, Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => ?_), add_zero]
  · exact gen _ (by simp) _ _ _
  · rw [hα (i.succ : ℕ) _ rfl U _ (by simp), map_zero, LinearMap.zero_apply, smul_zero]

end GlobalTheory.AWFront
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alexanderWhitney_cup_degree_zero_support_cochain : ∀ {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {S : Spc} {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj S) I n) (β : Cochain ((chains R).obj S) J m) (γ : Cochain ((chains R).obj S) K k), μ.IsAW hk α β γ → (∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S s U), 0 < s → ev α s t h U x = 0) → ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx S N U), ev γ N w h U x = μ.mul U n (-(N : ℤ) + m) w (by omega) (ev α 0 n (by simp) U (x.sub 0 0 (by omega))) (ev β N _ rfl U x) := by
  first | (exact @GlobalTheory.AWFront.ev_of_front) | (exact GlobalTheory.AWFront.ev_of_front) | (intros; apply GlobalTheory.AWFront.ev_of_front  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

noncomputable section

namespace GlobalTheory.PBFc

theorem evT_finsetSum {R : Type} [CommRing R] {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} {ι : Type} (S : Finset ι)
    (γ : ι → Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (∑ j ∈ S, γ j) a b s h U y = ∑ j ∈ S, evT (γ j) a b s h U y := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, evT_zero]
  | insert x S hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, evT_add, ih]

theorem evT_phi : ∀ (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U), evT (phi q V ℓ i z n α) a b s h U y = ∑ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b : ℤ) + 2 * ((j : ℕ) : ℤ)) s (by push_cast at h; omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b _ rfl U (vertS V ℓ y)) := by
  intro q E N V B ℓ i z n α a b s h U y
  rw [phi_apply, evT_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [evT_crossT]
  have he : Even (2 * ((j : ℕ) : ℤ) * (a : ℤ)) := by
    rw [mul_assoc]; exact even_two_mul _
  rw [Int.negOnePow_even _ he, one_smul]

end GlobalTheory.PBFc

end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveBundleCochain_apply_bisimplex : ∀ (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U), evT (phi q V ℓ i z n α) a b s h U y = ∑ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b : ℤ) + 2 * ((j : ℕ) : ℤ)) s (by push_cast at h; omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b _ rfl U (vertS V ℓ y)) := by
  first | (exact @GlobalTheory.PBFc.evT_phi) | (exact GlobalTheory.PBFc.evT_phi) | (intros; apply GlobalTheory.PBFc.evT_phi  <;> assumption)
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

namespace GlobalTheory.PBFg

theorem ev_finset_sum {R : Type} [CommRing R] {S : Spc} {I : Cx R} {n : ℤ} {ι : Type} [DecidableEq ι] (s : Finset ι)
    (c : ι → Cochain ((chains R).obj S) I n) (p : ℕ) (t : ℤ) (h : -(p : ℤ) + n = t) (U : Scheme.{0}) (x : Sx S p U) :
    ev (∑ j ∈ s, c j) p t h U x = ∑ j ∈ s, ev (c j) p t h U x := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ev_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ev_add, ih]

theorem col_identity (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (a : ℕ) (n m : ℤ) (hnm : n + -(a : ℤ) = m)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (c : ∀ j : Fin N, Cochain (sgl (((chains (ZMod q)).obj E).X (-(a : ℤ)))) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (m - 2 * ((j : ℕ) : ℤ)))
    (ha : ∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X (-(a : ℤ))) ≫ (c j).v 0 r hr = (α j).v (-(a : ℤ)) r hr')
    (β : Cochain ((biChains (ZMod q) (twX E V)).X (-(a : ℤ))) (res _ (tw q i)) m)
    (hb : ∀ (k t : ℤ) (h : -(a : ℤ) + k = t) r hr hr', β.v k r hr =
      (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) k t h ≫ (phi q V ℓ i z n α).v t r hr')
    (γ : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a)))) (res _ (tw q i)) m)
    (hγ : ∀ j : Fin N, (twPairI q i ((j : ℕ) : ℤ)).IsAW (sub_add_cancel m _)
      ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
        ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _))
      ((Cochain.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))).comp (z j) (zero_add _)) (γ j)) :
    (Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j) (zero_add m) = β := by
  ext k r hkr : 1
  by_cases hk : k ≤ 0
  · obtain ⟨b', rfl⟩ : ∃ b' : ℕ, k = -(b' : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [← cancel_epi (biChainsXIso (ZMod q) (twX E V) a b').inv]
    refine free_ext _ _ fun U y => ?_
    have e1 : Sec.map ((biChainsXIso (ZMod q) (twX E V) a b').inv ≫
        ((Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j) (zero_add m)).v (-(b' : ℤ)) r hkr)
        (freeGen (ZMod q) _ U y) = ev (∑ j, γ j) b' r hkr U y := by
      rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, reassoc_of% colCx_f]
      rfl
    have e2 : Sec.map ((biChainsXIso (ZMod q) (twX E V) a b').inv ≫ β.v (-(b' : ℤ)) r hkr) (freeGen (ZMod q) _ U y) =
        evT (phi q V ℓ i z n α) a b' r (by push_cast; omega) U y := by
      rw [hb (-(b' : ℤ)) (-((a + b' : ℕ) : ℤ)) (by push_cast; ring) r hkr (by push_cast; omega)]
      rfl
    rw [e1, e2, ev_finset_sum, GlobalTheory.T.projectiveBundleCochain_apply_bisimplex]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hA : ∀ (s : ℕ) (t : ℤ) (h : -(s : ℤ) + (m - 2 * ((j : ℕ) : ℤ)) = t) (U' : Scheme.{0})
        (x : Sx ((twX E V).obj (op (SimplexCategory.mk a))) s U'), 0 < s →
        ev ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
          ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _)) s t h U' x = 0 := by
      intro s t h U' x hs
      erw [ev_pull]
      exact ev_prE_pos _ E a (c j) s t h U' _ hs
    rw [GlobalTheory.T.alexanderWhitney_cup_degree_zero_support_cochain (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel m _) _ _ (γ j) (hγ j) hA b' r hkr U y]
    have hAv : ∀ (h0 : -((0 : ℕ) : ℤ) + (m - 2 * ((j : ℕ) : ℤ)) = m - 2 * ((j : ℕ) : ℤ)) (h00 : 0 + 0 ≤ b'),
        EtC.ev ((Cochain.ofHom ((chains (ZMod q)).map (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N)))).comp
          ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) (zero_add _)) 0 (m - 2 * ((j : ℕ) : ℤ)) h0 U
          (Sx.sub (E := (twX E V).obj (op (SimplexCategory.mk a))) y 0 0 h00) =
        Sec.map ((chainsXIso (ZMod q) E a).inv ≫ sglι _ ≫ (c j).v 0 (m - 2 * ((j : ℕ) : ℤ)) (by simpa using h0))
          (freeGen (ZMod q) _ U (baseS V y)) := fun h0 h00 =>
      (ev_pull (ptimes.fst (E.obj (op (SimplexCategory.mk a))) (Fib N))
        ((Cochain.ofHom (prE _ E a)).comp (c j) (zero_add _)) 0 _ h0 U
        (Sx.sub (E := (twX E V).obj (op (SimplexCategory.mk a))) y 0 0 h00)).trans
        (ev_prE_zero _ E a (c j) _ h0 U _)
    have hZv : ∀ (h2 : -(b' : ℤ) + 2 * ((j : ℕ) : ℤ) = -(b' : ℤ) + 2 * ((j : ℕ) : ℤ)),
        EtC.ev ((Cochain.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))).comp (z j) (zero_add _)) b'
          (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) h2 U y = EtC.ev (z j) b' _ rfl U (vertS V ℓ y) := fun h2 =>
      ev_pull (ℓ.app (op (SimplexCategory.mk a))) (z j) b' _ h2 U y
    refine (congrArg₂ (fun u v => (twPairI q i ((j : ℕ) : ℤ)).mul U (m - 2 * ((j : ℕ) : ℤ))
      (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r (by omega) u v) (hAv _ _) (hZv _)).trans ?_
    have key : ∀ (s : ℤ) (hs : -(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ)) = s) (h0 : 0 + (m - 2 * ((j : ℕ) : ℤ)) = s)
        (h1 : s + (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) = r),
        (twPairI q i ((j : ℕ) : ℤ)).mul U s (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r h1
          (Sec.map ((chainsXIso (ZMod q) E a).inv ≫ sglι _ ≫ (c j).v 0 s h0) (freeGen (ZMod q) _ U (baseS V y)))
          (ev (z j) b' _ rfl U (vertS V ℓ y)) =
        (twPairI q i ((j : ℕ) : ℤ)).mul U (-(a : ℤ) + (n - 2 * ((j : ℕ) : ℤ))) (-(b' : ℤ) + 2 * ((j : ℕ) : ℤ)) r
          (by omega) (ev (α j) a _ rfl U (baseS V y)) (ev (z j) b' _ rfl U (vertS V ℓ y)) := by
      intro s hs
      subst hs
      intro h0 h1
      rw [ha j _ h0 (by omega)]
      rfl
    exact key _ (by omega) _ _
  · exact (biChains_isZero (twX E V) (-(a : ℤ)) k (Or.inr (by omega))).eq_of_src _ _

theorem graded_bijective : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ (a : ℕ) (j : Fin N), CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ)) (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀), ∀ p ≤ (0 : ℤ), ∃ ψ : ∀ m, (∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) → CohomologyClass ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m, (∀ m, Function.Bijective (ψ m)) ∧ ∀ n m, n + p = m → ∀ α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)), (∀ j c r hr, p < c → (α j).v c r hr = 0) → ∀ (a : ∀ j : Fin N, Cocycle (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (b : Cocycle ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m), (∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X p) ≫ (a j).1.v 0 r hr = (α j).v p r hr') → (∀ (k t : ℤ) (h : p + k = t) r hr hr', b.1.v k r hr = (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) p k t h ≫ (phi q V ℓ i (fun j => (z j).1) n α).v t r hr') → ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
  intro q _ E N V hE B ℓ i z hz hD p hp
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, p = -(a : ℤ) := ⟨(-p).toNat, by omega⟩
  set P : PSh := E.obj (op (SimplexCategory.mk a)) with hPdef
  have hP : Inv q (disc.obj P) := fun U ⟨x⟩ =>
    hE U ⟨(E.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk a) 0).op).app (op U) x⟩
  have hpbf := hD P (trivV N (disc.obj P)) hP
  have hpi : ∀ m, Function.Bijective (fun (x : ∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X (-(a : ℤ))))
      (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (j : Fin N) => cpull (prE _ E a) _ _ (x j)) := by
    intro m
    have hb := fun (j : Fin N) => LevelCmp.cpull_bij_of_heq (prEquiv (ZMod q) E a) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (m - 2 * ((j : ℕ) : ℤ))
    refine ⟨fun x y hxy => funext fun j => (hb j).1 (congrFun hxy j), fun y => ?_⟩
    exact ⟨fun j => ((hb j).2 (y j)).choose, funext fun j => ((hb j).2 (y j)).choose_spec⟩
  refine ⟨fun m x => cpull (colCx _ (twX E V) a).hom _ m (pull _ (colIso P (trivV N (disc.obj P))).hom _ m
    (pbfMap q (trivV N (disc.obj P)) m i (fun j => cpull (prE _ E a) _ _ (x j)))), fun m => ?_, ?_⟩
  · exact (LevelCmp.cpull_bij_of_heq (HomotopyEquiv.ofIso (colCx _ (twX E V) a)) _ m).comp
      ((LevelCmp.cpull_bij_of_heq (HomotopyEquiv.ofIso ((chains (ZMod q)).mapIso (colIso P (trivV N (disc.obj P))))) _ m).comp
        ((hpbf m i).comp (hpi m)))
  · intro n m hnm α hα ac b ha hb
    let A : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a))))
        (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ)) := fun j =>
      zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ptimes.fst P (Fib N))))
        (zcomp (Cocycle.ofHom (prE _ E a)) (ac j) (zero_add _)) (zero_add _)
    let Z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj ((twX E V).obj (op (SimplexCategory.mk a))))
        (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)) := fun j =>
      zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)
    choose γ hγ using fun j : Fin N => Pair.aw_exists (twPairI q i ((j : ℕ) : ℤ)) ((twX E V).obj (op (SimplexCategory.mk a)))
      (sub_add_cancel m (2 * ((j : ℕ) : ℤ))) (A j) (Z j)
    have hterm : ∀ j : Fin N, ((cup q (pull _ (ptimes.fst P (Fib N)) _ _
        (cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j))))
        (cpow q (c1 q (ptimes.snd P (Fib N) ≫ Fib.line N)) j)).cast (by ring) (by ring) : Ht q (ptimes P (Fib N)) m i) =
        CohomologyClass.mk (γ j) := by
      intro j
      rw [← hz a j]
      exact GlobalTheory.T.cupProduct_cast_mk_of_isAlexanderWhitney q i j m (A j) (Z j) (γ j) (hγ j)
    change cpull _ _ m (pull _ _ _ m (pbfMap q (trivV N (disc.obj P)) m i
      (fun j => cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j))))) = _
    have h1 := pull_colIso_pbfMap q P (trivV N (disc.obj P)) hP m i
      (fun j => cpull (prE _ E a) _ _ (CohomologyClass.mk (ac j)))
    erw [h1]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    erw [mk_sum_cocycle]
    change CohomologyClass.mk (zcomp _ _ _) = _
    congr 1
    apply Cocycle.ext
    change (Cochain.ofHom (colCx _ (twX E V) a).hom).comp (∑ j, γ j).1 (zero_add m) = b.1
    erw [AddSubgroup.val_finset_sum]
    exact col_identity q V ℓ i (fun j => (z j).1) a n m hnm α (fun j => (ac j).1) ha b.1 hb (fun j => (γ j).1) hγ

end GlobalTheory.PBFg
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_cocycle_simplicial_levels_cup : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ (a : ℕ) (j : Fin N), CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ)) (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀), ∀ p ≤ (0 : ℤ), ∃ ψ : ∀ m, (∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) → CohomologyClass ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m, (∀ m, Function.Bijective (ψ m)) ∧ ∀ n m, n + p = m → ∀ α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)), (∀ j c r hr, p < c → (α j).v c r hr = 0) → ∀ (a : ∀ j : Fin N, Cocycle (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (b : Cocycle ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m), (∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X p) ≫ (a j).1.v 0 r hr = (α j).v p r hr') → (∀ (k t : ℤ) (h : p + k = t) r hr hr', b.1.v k r hr = (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) p k t h ≫ (phi q V ℓ i (fun j => (z j).1) n α).v t r hr') → ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
  first | (exact @GlobalTheory.PBFg.graded_bijective) | (exact GlobalTheory.PBFg.graded_bijective) | (intros; apply GlobalTheory.PBFg.graded_bijective  <;> assumption)
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFc
open GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ

instance res_isStrictlyGE (R : Type) [CommRing R] (F : Shv R) : (res R F).IsStrictlyGE 0 := by
  unfold res; infer_instance

instance chains_isStrictlyLE (R : Type) [CommRing R] (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

variable (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
  (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)

theorem phi_δ (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n m : ℤ) (hnm : n + 1 = m)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    phi q V ℓ i (fun j => (z j).1) m (fun j => δ (n - 2 * ((j : ℕ) : ℤ)) (m - 2 * ((j : ℕ) : ℤ)) (α j)) =
      δ n m (phi q V ℓ i (fun j => (z j).1) n α) := by
  have hs : ∀ (f : Fin N → Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n),
      δ n m (∑ j, f j) = ∑ j, δ n m (f j) := fun f => map_sum (AddMonoidHom.mk' (δ n m) (δ_add n m)) f _
  rw [phi_apply, phi_apply, hs]
  refine Finset.sum_congr rfl fun j _ => ?_
  change _ = δ n m _
  rw [GlobalTheory.T.crossProductTwisted_leibniz_rule V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _)
    (show n - 2 * ((j : ℕ) : ℤ) + 1 = m - 2 * ((j : ℕ) : ℤ) by omega) rfl hnm (by omega) (by omega),
    Cocycle.δ_eq_zero (z j), crossT_zero_right, smul_zero, add_zero]

theorem phi_van (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (p n : ℤ)
    (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)))
    (hα : ∀ j c r hr, p < c → (α j).v c r hr = 0) (c l t : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, l) = t) (r : ℤ) (hr : t + n = r) (hc : p < c) :
    (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ (phi q V ℓ i z n α).v t r hr = 0 := by
  let ev₀ : Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n →+ _ :=
    AddMonoidHom.mk' (fun γ => (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) c l t h ≫ γ.v t r hr)
      (fun γ γ' => by rw [Cochain.add_v, Preadditive.comp_add])
  change ev₀ _ = 0
  rw [phi_apply, map_sum]
  exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.cochain_product_vanishing_above_degree V ℓ _ _ (α j) (z j) p (hα j) c l t h r hr hc

theorem pull_iso_bijective {E E' : Spc} (e : E ≅ E') (F : Shv (ZMod q)) (n : ℤ) :
    Function.Bijective (pull (ZMod q) e.hom F n) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨pull (ZMod q) e.inv F n y, ?_⟩⟩
  · have hx := (pull_comp (ZMod q) e.inv e.hom F n x).symm
    have hy := (pull_comp (ZMod q) e.inv e.hom F n y).symm
    rw [e.inv_hom_id, pull_id] at hx hy
    exact hx.symm.trans ((congrArg _ hxy).trans hy)
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem pbf_of_model [NeZero q] (hE : Inv q E)
    (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (hzd : ∀ j : Fin N, CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map
        (bidiag.map ℓ ≫ (bidiagConst B).hom))) (z j) (zero_add _)) =
      pull _ (twIso E V).hom _ _ (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) (j : ℕ)))
    (hzc : ∀ (a : ℕ) (j : Fin N),
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j)
        (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ))
    (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀) : PBF q V := by
  intro n i
  have hf1 := pull_iso_bijective q (twIso E V) (tw q i) n
  have hf2 := pull_awChains_bijective (ZMod q) (twX E V) (res _ (tw q i)) n
  let φ : (∀ j : Fin N, CohomologyClass ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (n - 2 * ((j : ℕ) : ℤ))) → CohomologyClass (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n :=
    fun x => Function.surjInv hf2.2 (pull _ (twIso E V).hom _ n (pbfMap q V n i x))
  have hφ : ∀ (a : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ))))
      (n - 2 * ((j : ℕ) : ℤ))) (b : Cocycle (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n),
      b.1 = phi q V ℓ i (fun j => (z j).1) n (fun j => (a j).1) →
      φ (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
    intro a b hb
    apply hf2.1
    rw [Function.surjInv_eq hf2.2]
    exact GlobalTheory.T.twisted_cocycle_classes_pullback_cup q V ℓ n i z hzd a b hb
  have hb : Function.Bijective φ :=
    GlobalTheory.ColFilt.bijective_total_of_terms (ZMod q) (biChains (ZMod q) (twX E V))
      (fun p k h => biChains_isZero (twX E V) p k h) ((chains (ZMod q)).obj E)
      (fun j : Fin N => res _ (tw q (i - ((j : ℕ) : ℤ)))) (res _ (tw q i)) (fun j : Fin N => 2 * ((j : ℕ) : ℤ))
      (phi q V ℓ i (fun j => (z j).1)) (fun n m h α => phi_δ q V ℓ i z n m h α)
      (fun p n α hα => phi_van q V ℓ i (fun j => (z j).1) p n α hα)
      (GlobalTheory.T.twisted_cocycle_simplicial_levels_cup q V hE ℓ i z hzc hD) n φ hφ
  have hcomp : (pull _ (twIso E V).hom _ n) ∘ pbfMap q V n i = (cpull (awChains (ZMod q) (twX E V)) (res _ (tw q i)) n) ∘ φ :=
    funext fun x => (Function.surjInv_eq hf2.2 _).symm
  exact (Function.Bijective.of_comp_iff' hf1 _).1 (hcomp ▸ hf2.comp hb)

end GlobalTheory.PBFc

end
end
