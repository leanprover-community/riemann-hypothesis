import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TPullTMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans
import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsCohomologyZeroEquivSectionsNatural
import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsCoefficientEquivCohomologyOfElements

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH
open GlobalTheory.CatH (face toLast)

namespace UpperTheory.Ru.crystallineComparison.Th

variable {C : Type 1} [Category.{0} C]

theorem fa_ext {X : Type 1} {A : AddCommGrpCat.{1}} {f g : AddCommGrpCat.of (FreeAbelianGroup X) ⟶ A}
    (h : ∀ x, f.hom (FreeAbelianGroup.of x) = g.hom (FreeAbelianGroup.of x)) : f = g := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of x => exact h x
  | neg x ih => simpa using congrArg Neg.neg (h x)
  | add x y hx hy => simp only [map_add, hx, hy]

variable (P : C ⥤ Type)

abbrev Gen (k : ℕ) (B : C) : Type 1 := Σ s : ComposableArrows P.Elements k, ((s.obj (Fin.last k)).1 ⟶ B)

def L (k : ℕ) : Coef C where
  obj B := AddCommGrpCat.of (FreeAbelianGroup (Gen P k B))
  map φ := AddCommGrpCat.ofHom (FreeAbelianGroup.map fun g => ⟨g.1, g.2 ≫ φ⟩)
  map_id B := fa_ext fun x => by simp
  map_comp φ ψ := fa_ext fun x => by simp

def gFace {k : ℕ} {B : C} (i : Fin (k + 2)) (g : Gen P (k + 1) B) : Gen P k B :=
  ⟨face i g.1, (toLast i g.1).1 ≫ g.2⟩

def dL (k : ℕ) : L P (k + 1) ⟶ L P k where
  app B := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun g => ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • FreeAbelianGroup.of (gFace P i g))
  naturality B B' φ := fa_ext fun g => by
    simp [L, gFace]

variable {P}

def tOf {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) : L P k ⟶ K where
  app B := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun g => (K.map g.2).hom (f g.1))
  naturality B B' φ := fa_ext fun g => by
    simp [L]

def cOf {K : Coef C} {k : ℕ} (u : L P k ⟶ K) : Cn (elF P (zm K)) k :=
  fun s => (u.app (s.obj (Fin.last k)).1).hom (FreeAbelianGroup.of ⟨s, 𝟙 _⟩)

theorem L_map_of {B B' : C} (φ : B ⟶ B') {k : ℕ} (g : Gen P k B) :
    ((L P k).map φ).hom (FreeAbelianGroup.of g) = FreeAbelianGroup.of (⟨g.1, g.2 ≫ φ⟩ : Gen P k B') :=
  FreeAbelianGroup.map_of_apply _

theorem dL_of {k : ℕ} {B : C} (g : Gen P (k + 1) B) :
    ((dL P k).app B).hom (FreeAbelianGroup.of g) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • (FreeAbelianGroup.of (gFace P i g) : (L P k).obj B) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem tOf_of {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) {B : C} (g : Gen P k B) :
    ((tOf f).app B).hom (FreeAbelianGroup.of g) = (K.map g.2).hom (f g.1) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem cOf_tOf {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) : cOf (tOf f) = f := by
  funext s
  refine (tOf_of f _).trans ?_
  simp only [K.map_id]
  rfl

theorem u_of {K : Coef C} {k : ℕ} (u : L P k ⟶ K) {B : C} (g : Gen P k B) :
    (u.app B).hom (FreeAbelianGroup.of g) = (K.map g.2).hom (cOf u g.1) := by
  obtain ⟨s, a⟩ := g
  have h2 : ((L P k).map a).hom (FreeAbelianGroup.of (⟨s, 𝟙 _⟩ : Gen P k _)) = FreeAbelianGroup.of (⟨s, a⟩ : Gen P k B) := by
    rw [L_map_of]; simp
  have h3 := congrArg (fun f => f.hom (FreeAbelianGroup.of (⟨s, 𝟙 _⟩ : Gen P k _))) (u.naturality a)
  refine Eq.trans ?_ h3
  exact (congrArg (u.app B).hom h2).symm

theorem tOf_cOf {K : Coef C} {k : ℕ} (u : L P k ⟶ K) : tOf (cOf u) = u := by
  ext B : 2
  exact fa_ext fun g => (tOf_of _ g).trans (u_of u g).symm

theorem d_apply' {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) (s : ComposableArrows P.Elements (k + 1)) :
    d (elF P (zm K)) k f s = ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • (K.map (toLast i s).1).hom (f (face i s)) := rfl

theorem d_cOf {K : Coef C} {k : ℕ} (u : L P k ⟶ K) : d (elF P (zm K)) k (cOf u) = cOf (dL P k ≫ u) := by
  funext s
  rw [d_apply']
  change _ = (u.app _).hom (((dL P k).app _).hom (FreeAbelianGroup.of (⟨s, 𝟙 _⟩ : Gen P (k + 1) _)))
  rw [dL_of, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, u_of]
  simp [gFace]

theorem tOf_d {K : Coef C} {k : ℕ} (f : Cn (elF P (zm K)) k) : tOf (d (elF P (zm K)) k f) = dL P k ≫ tOf f := by
  ext B : 2
  refine fa_ext fun g => (tOf_of _ g).trans ?_
  change _ = ((tOf f).app B).hom (((dL P k).app B).hom (FreeAbelianGroup.of g))
  rw [d_apply', dL_of, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, tOf_of]
  simp [gFace]

theorem tOf_zero {K : Coef C} {k : ℕ} : tOf (0 : Cn (elF P (zm K)) k) = 0 := by
  ext B : 2
  refine fa_ext fun g => (tOf_of _ g).trans ?_
  exact map_zero _

theorem dL_dL (k : ℕ) : dL P (k + 1) ≫ dL P k = 0 := by
  have h := tOf_d (d (elF P (zm (L P k))) k (cOf (𝟙 _)))
  rw [CrystallineSemistableComparison.CH.d_d, tOf_zero, tOf_d, tOf_cOf, Category.comp_id] at h
  exact h.symm

theorem vanish_of_exact (hex : ∀ k, (ShortComplex.mk (dL P (k + 1)) (dL P k) (dL_dL k)).Exact)
    (K : Coef C) (hK : Injective K) (j : ℕ) : Subsingleton (TH P K (j + 1)) := by
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ x : TH P K (j + 1), x = 0 by rw [h x, h y]
  intro x
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (elF P (zm K))) (j + 1)).1 x
  rw [(CrystallineSemistableComparison.P.cls_surj (cx (elF P (zm K))) (j + 1)).2.1]
  have h0 : dL P (j + 1) ≫ tOf f = 0 := by
    rw [← tOf_d]
    exact (congrArg tOf hf).trans tOf_zero
  refine ⟨cOf ((hex j).descToInjective (tOf f) h0), ?_⟩
  refine (d_cOf _).trans ?_
  have := (hex j).comp_descToInjective (tOf f) h0
  simp only at this
  rw [this, cOf_tOf]

end UpperTheory.Ru.crystallineComparison.Th
end
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory
open GlobalTheory.CatH (face toLast)

namespace UpperTheory.Ru.crystallineComparison.Th

section Snoc

variable {E : Type*} [Category E] {m : ℕ} (s : ComposableArrows E m) {X : E} (a : s.obj (Fin.last m) ⟶ X)

def snObj (X : E) (i : Fin (m + 2)) : E := if h : (i : ℕ) < m + 1 then s.obj ⟨i, h⟩ else X

theorem snObj_lt (X : E) {i : Fin (m + 2)} (h : (i : ℕ) < m + 1) : snObj s X i = s.obj ⟨i, h⟩ := dif_pos h

theorem snObj_ge (X : E) {i : Fin (m + 2)} (h : ¬ (i : ℕ) < m + 1) : snObj s X i = X := dif_neg h

def snMap (i j : Fin (m + 2)) (hij : i ≤ j) : snObj s X i ⟶ snObj s X j :=
  if hj : (j : ℕ) < m + 1 then
    eqToHom (snObj_lt s X (lt_of_le_of_lt (Fin.le_def.1 hij) hj)) ≫
      s.map (homOfLE (show (⟨i, lt_of_le_of_lt (Fin.le_def.1 hij) hj⟩ : Fin (m + 1)) ≤ ⟨j, hj⟩ from Fin.le_def.2 (Fin.le_def.1 hij))) ≫
        eqToHom (snObj_lt s X hj).symm
  else if hi : (i : ℕ) < m + 1 then
    eqToHom (snObj_lt s X hi) ≫ s.map (homOfLE (Fin.le_last _)) ≫ a ≫ eqToHom (snObj_ge s X hj).symm
  else eqToHom ((snObj_ge s X hi).trans (snObj_ge s X hj).symm)

theorem snMap_lt {i j : Fin (m + 2)} (hij : i ≤ j) (hj : (j : ℕ) < m + 1) :
    snMap s a i j hij = eqToHom (snObj_lt s X (lt_of_le_of_lt (Fin.le_def.1 hij) hj)) ≫
      s.map (homOfLE (show (⟨i, lt_of_le_of_lt (Fin.le_def.1 hij) hj⟩ : Fin (m + 1)) ≤ ⟨j, hj⟩ from Fin.le_def.2 (Fin.le_def.1 hij))) ≫
        eqToHom (snObj_lt s X hj).symm := dif_pos hj

theorem snMap_mid {i j : Fin (m + 2)} (hij : i ≤ j) (hj : ¬ (j : ℕ) < m + 1) (hi : (i : ℕ) < m + 1) :
    snMap s a i j hij = eqToHom (snObj_lt s X hi) ≫ s.map (homOfLE (Fin.le_last _)) ≫ a ≫ eqToHom (snObj_ge s X hj).symm := by
  rw [snMap, dif_neg hj, dif_pos hi]

theorem snMap_top {i j : Fin (m + 2)} (hij : i ≤ j) (hj : ¬ (j : ℕ) < m + 1) (hi : ¬ (i : ℕ) < m + 1) :
    snMap s a i j hij = eqToHom ((snObj_ge s X hi).trans (snObj_ge s X hj).symm) := by
  rw [snMap, dif_neg hj, dif_neg hi]

def snoc : ComposableArrows E (m + 1) where
  obj := snObj s X
  map {i j} f := snMap s a i j (leOfHom f)
  map_id i := by
    by_cases hi : (i : ℕ) < m + 1
    · rw [snMap_lt s a _ hi]
      simp [homOfLE_refl]
    · rw [snMap_top s a _ hi hi]
      simp
  map_comp {i j k} f g := by
    have hij := leOfHom f
    have hjk := leOfHom g
    by_cases hk : (k : ℕ) < m + 1
    · have hj : (j : ℕ) < m + 1 := lt_of_le_of_lt (Fin.le_def.1 hjk) hk
      rw [snMap_lt s a _ hk, snMap_lt s a _ hk, snMap_lt s a _ hj]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Functor.map_comp_assoc]
      rfl
    · by_cases hj : (j : ℕ) < m + 1
      · have hi : (i : ℕ) < m + 1 := lt_of_le_of_lt (Fin.le_def.1 hij) hj
        rw [snMap_mid s a _ hk hi, snMap_mid s a _ hk hj, snMap_lt s a _ hj]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Functor.map_comp_assoc]
        rfl
      · by_cases hi : (i : ℕ) < m + 1
        · rw [snMap_mid s a _ hk hi, snMap_mid s a _ hj hi, snMap_top s a _ hk hj]
          simp
        · rw [snMap_top s a _ hk hi, snMap_top s a _ hj hi, snMap_top s a _ hk hj]
          simp

theorem snoc_last : (snoc s a).obj (Fin.last (m + 1)) = X := snObj_ge s X (by simp)

end Snoc
section Chains

variable {E : Type*} [Category E]

theorem chain_ext {n : ℕ} {T T' : ComposableArrows E n} (ho : ∀ i, T.obj i = T'.obj i)
    (hm : ∀ i j (h : i ≤ j), T.map (homOfLE h) = eqToHom (ho i) ≫ T'.map (homOfLE h) ≫ eqToHom (ho j).symm) : T = T' :=
  CategoryTheory.Functor.ext ho fun i j f => hm i j (leOfHom f)

theorem sigma_chain_eq {n : ℕ} {X : E} {s s' : ComposableArrows E n} {b : s.obj (Fin.last n) ⟶ X}
    {b' : s'.obj (Fin.last n) ⟶ X} (h : s = s') (w : b = eqToHom (by rw [h]) ≫ b') :
    (⟨s, b⟩ : Σ t : ComposableArrows E n, t.obj (Fin.last n) ⟶ X) = ⟨s', b'⟩ := by
  subst h
  simp only [eqToHom_refl, Category.id_comp] at w
  rw [w]

variable {m : ℕ} (s : ComposableArrows E m) {X : E} (a : s.obj (Fin.last m) ⟶ X)

theorem snObj_val {p : Fin (m + 2)} {q : Fin (m + 1)} (h : (p : ℕ) = q) : snObj s X p = s.obj q :=
  (snObj_lt s X (h ▸ q.2)).trans (congrArg s.obj (Fin.ext h))

theorem snMap_val {p p' : Fin (m + 2)} {q q' : Fin (m + 1)} (h : (p : ℕ) = q) (h' : (p' : ℕ) = q') (hp : p ≤ p') (hq : q ≤ q') :
    snMap s a p p' hp = eqToHom (snObj_val s h) ≫ s.map (homOfLE hq) ≫ eqToHom (snObj_val s h').symm := by
  obtain ⟨q, hq0⟩ := q
  obtain ⟨q', hq1⟩ := q'
  obtain rfl : (p : ℕ) = q := h
  obtain rfl : (p' : ℕ) = q' := h'
  exact snMap_lt s a hp hq1

theorem snMap_val_top {p p' : Fin (m + 2)} {q : Fin (m + 1)} (h : (p : ℕ) = q) (h' : ¬ (p' : ℕ) < m + 1) (hp : p ≤ p') :
    snMap s a p p' hp = eqToHom (snObj_val s h) ≫ s.map (homOfLE (Fin.le_last q)) ≫ a ≫ eqToHom (snObj_ge s X h').symm := by
  obtain ⟨q, hq0⟩ := q
  obtain rfl : (p : ℕ) = q := h
  exact snMap_mid s a hp h' hq0

def snε : (snoc s a).obj (Fin.last (m + 1)) ⟶ X := eqToHom (snoc_last s a)

theorem face_snoc_last : face (Fin.last (m + 1)) (snoc s a) = s := by
  have hv : ∀ i : Fin (m + 1), (((Fin.last (m + 1)).succAbove i : Fin (m + 2)) : ℕ) = i := fun i => by simp
  refine chain_ext (fun i => snObj_val s (hv i)) fun i j h => ?_
  exact snMap_val s a (hv i) (hv j) ((Fin.strictMono_succAbove _).monotone h) h

theorem gen_snoc_last :
    (⟨face (Fin.last (m + 1)) (snoc s a), toLast (Fin.last (m + 1)) (snoc s a) ≫ snε s a⟩ :
      Σ t : ComposableArrows E m, t.obj (Fin.last m) ⟶ X) = ⟨s, a⟩ := by
  refine sigma_chain_eq (face_snoc_last s a) ?_
  have hv : (((Fin.last (m + 1)).succAbove (Fin.last m) : Fin (m + 2)) : ℕ) = (Fin.last m : Fin (m + 1)) := by simp
  have e : toLast (Fin.last (m + 1)) (snoc s a) = eqToHom (snObj_val s hv) ≫ s.map (homOfLE (Fin.le_last _)) ≫ a ≫
      eqToHom (snObj_ge s X (by simp)).symm := snMap_val_top s a hv (by simp) (Fin.le_last _)
  rw [e]
  simp [snε, homOfLE_refl]

theorem snoc_reindex {n : ℕ} (f : Fin (n + 1) → Fin (m + 1)) (hf : Monotone f) (g : Fin (n + 2) → Fin (m + 2)) (hg : Monotone g)
    (h1 : ∀ (p : Fin (n + 2)) (hp : (p : ℕ) < n + 1), (g p : ℕ) = f ⟨p, hp⟩)
    (h2 : ∀ p : Fin (n + 2), ¬ (p : ℕ) < n + 1 → ¬ (g p : ℕ) < m + 1) :
    hg.functor ⋙ snoc s a = snoc (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a) := by
  have ho : ∀ p, (hg.functor ⋙ snoc s a).obj p = (snoc (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a)).obj p := by
    intro p
    by_cases hp : (p : ℕ) < n + 1
    · exact (snObj_val s (h1 p hp)).trans (snObj_lt (hf.functor ⋙ s) X hp).symm
    · exact (snObj_ge s X (h2 p hp)).trans (snObj_ge (hf.functor ⋙ s) X hp).symm
  refine chain_ext ho fun p p' h => ?_
  have e1 : (hg.functor ⋙ snoc s a).map (homOfLE h) = snMap s a (g p) (g p') (hg h) := rfl
  have e2 : (snoc (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a)).map (homOfLE h) =
    snMap (hf.functor ⋙ s) (s.map (homOfLE (Fin.le_last (f (Fin.last n)))) ≫ a) p p' h := rfl
  rw [e1, e2]
  by_cases hp' : (p' : ℕ) < n + 1
  · have hp : (p : ℕ) < n + 1 := lt_of_le_of_lt (Fin.le_def.1 h) hp'
    rw [snMap_val s a (h1 p hp) (h1 p' hp') (hg h) (hf (Fin.le_def.2 (Fin.le_def.1 h))), snMap_lt _ _ h hp']
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl
  · by_cases hp : (p : ℕ) < n + 1
    · rw [snMap_val_top s a (h1 p hp) (h2 p' hp') (hg h), snMap_mid _ _ h hp' hp]
      simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
      have e3 : s.map (homOfLE (Fin.le_last (f ⟨p, hp⟩))) =
          (hf.functor ⋙ s).map (homOfLE (Fin.le_last (⟨p, hp⟩ : Fin (n + 1)))) ≫ s.map (homOfLE (Fin.le_last (f (Fin.last n)))) := by
        change _ = s.map _ ≫ s.map _
        rw [← Functor.map_comp]
        rfl
      rw [e3]
      simp only [Category.assoc]
    · rw [snMap_top s a (hg h) (h2 p' hp') (h2 p hp), snMap_top _ _ h hp' hp]
      simp

end Chains

section Face

variable {E : Type*} [Category E] {m : ℕ} (s : ComposableArrows E (m + 1)) {X : E} (a : s.obj (Fin.last (m + 1)) ⟶ X)

private theorem sa_lt (i : Fin (m + 2)) (p : Fin (m + 2)) (hp : (p : ℕ) < m + 1) :
    ((i.castSucc.succAbove p : Fin (m + 3)) : ℕ) = (i.succAbove ⟨p, hp⟩ : Fin (m + 2)) := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

private theorem sa_ge (i : Fin (m + 2)) (p : Fin (m + 2)) (hp : ¬ (p : ℕ) < m + 1) :
    ¬ ((i.castSucc.succAbove p : Fin (m + 3)) : ℕ) < m + 2 := by
  have h1 : (p : ℕ) = m + 1 := by omega
  have h2 := i.2
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp <;> omega

theorem face_snoc_castSucc (i : Fin (m + 2)) : face i.castSucc (snoc s a) = snoc (face i s) (toLast i s ≫ a) :=
  snoc_reindex s a (Fin.succAboveOrderEmb i) (Fin.succAboveOrderEmb i).monotone (Fin.succAboveOrderEmb i.castSucc)
    (Fin.succAboveOrderEmb i.castSucc).monotone (sa_lt i) (sa_ge i)

theorem gen_snoc_castSucc (i : Fin (m + 2)) :
    (⟨face i.castSucc (snoc s a), toLast i.castSucc (snoc s a) ≫ snε s a⟩ :
      Σ t : ComposableArrows E (m + 1), t.obj (Fin.last (m + 1)) ⟶ X) =
      ⟨snoc (face i s) (toLast i s ≫ a), snε _ _⟩ := by
  refine sigma_chain_eq (face_snoc_castSucc s a i) ?_
  have h0 : ¬ ((i.castSucc.succAbove (Fin.last (m + 1)) : Fin (m + 3)) : ℕ) < m + 2 := sa_ge i _ (by simp)
  have e : toLast i.castSucc (snoc s a) = eqToHom ((snObj_ge s X h0).trans (snObj_ge s X (by simp)).symm) :=
    snMap_top s a (Fin.le_last _) (by simp) h0
  rw [e]
  simp [snε]

end Face

end UpperTheory.Ru.crystallineComparison.Th
end
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.CH
open GlobalTheory.CatH (face toLast)

namespace UpperTheory.Ru.crystallineComparison.Th

variable {C : Type 1} [Category.{0} C]

theorem exact_of_app (S : ShortComplex (Coef C))
    (h : ∀ B, Function.Exact (S.f.app B).hom (S.g.app B).hom) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  refine CategoryTheory.Functor.isZero _ fun B => ?_
  have h1 : (S.map ((evaluation C AddCommGrpCat.{1}).obj B)).Exact :=
    (ShortComplex.ab_exact_iff_function_exact _).2 (h B)
  rw [ShortComplex.exact_iff_isZero_homology] at h1
  exact h1.of_iso (S.mapHomologyIso ((evaluation C AddCommGrpCat.{1}).obj B)).symm

variable {P : C ⥤ Type}

def snG {m : ℕ} {B : C} (g : Gen P m B) (z : P.obj B) (h : (P.map g.2) (g.1.obj (Fin.last m)).2 = z) : Gen P (m + 1) B :=
  ⟨snoc g.1 (X := (⟨B, z⟩ : P.Elements)) ⟨g.2, h⟩, (snε g.1 (X := (⟨B, z⟩ : P.Elements)) ⟨g.2, h⟩).1⟩

theorem snG_eq {m : ℕ} {B : C} (g : Gen P m B) {z : P.obj B} (h : (P.map g.2) (g.1.obj (Fin.last m)).2 = z) :
    snG g z h = snG g _ rfl := by
  subst h; rfl

def sn {m : ℕ} {B : C} (g : Gen P m B) : Gen P (m + 1) B := snG g _ rfl

theorem gFace_snG_last {m : ℕ} {B : C} (g : Gen P m B) (z : P.obj B) (h : (P.map g.2) (g.1.obj (Fin.last m)).2 = z) :
    gFace P (Fin.last (m + 1)) (snG g z h) = g :=
  congrArg (fun p : (Σ t : ComposableArrows P.Elements m, t.obj (Fin.last m) ⟶ (⟨B, z⟩ : P.Elements)) =>
    (⟨p.1, p.2.1⟩ : Gen P m B)) (gen_snoc_last g.1 (X := (⟨B, z⟩ : P.Elements)) ⟨g.2, h⟩)

theorem gFace_snG_castSucc {m : ℕ} {B : C} (g : Gen P (m + 1) B) (z : P.obj B) (h : (P.map g.2) (g.1.obj (Fin.last (m + 1))).2 = z)
    (i : Fin (m + 2)) (h' : (P.map (gFace P i g).2) ((gFace P i g).1.obj (Fin.last m)).2 = z) :
    gFace P i.castSucc (snG g z h) = snG (gFace P i g) z h' :=
  congrArg (fun p : (Σ t : ComposableArrows P.Elements (m + 1), t.obj (Fin.last (m + 1)) ⟶ (⟨B, z⟩ : P.Elements)) =>
    (⟨p.1, p.2.1⟩ : Gen P (m + 1) B)) (gen_snoc_castSucc g.1 (X := (⟨B, z⟩ : P.Elements)) ⟨g.2, h⟩ i)

theorem gFace_sn_last {m : ℕ} {B : C} (g : Gen P m B) : gFace P (Fin.last (m + 1)) (sn g) = g := gFace_snG_last g _ rfl

theorem gFace_sn_castSucc {m : ℕ} {B : C} (g : Gen P (m + 1) B) (i : Fin (m + 2)) :
    gFace P i.castSucc (sn g) = sn (gFace P i g) := by
  have h' : (P.map (gFace P i g).2) ((gFace P i g).1.obj (Fin.last m)).2 = (P.map g.2) (g.1.obj (Fin.last (m + 1))).2 := by
    have e := (toLast i g.1).2
    change (P.map ((toLast i g.1).1 ≫ g.2)) _ = _
    rw [P.map_comp]
    exact congrArg (P.map g.2) e
  exact (gFace_snG_castSucc g _ rfl i h').trans (snG_eq _ h')

def hh (B : C) (m : ℕ) : (L P m).obj B →+ (L P (m + 1)).obj B := (FreeAbelianGroup.map sn : FreeAbelianGroup (Gen P m B) →+ _)

theorem hh_of (B : C) (m : ℕ) (g : Gen P m B) : hh B m (FreeAbelianGroup.of g) = FreeAbelianGroup.of (sn g) :=
  FreeAbelianGroup.map_of_apply _

def ofL {k : ℕ} {B : C} (g : Gen P k B) : (L P k).obj B := FreeAbelianGroup.of g

theorem d_hh_of (B : C) (k : ℕ) (g : Gen P (k + 1) B) :
    ((dL P (k + 1)).app B).hom (hh B (k + 1) (ofL g)) = hh B k (((dL P k).app B).hom (ofL g)) + (-1 : ℤ) ^ (k + 2) • ofL g := by
  unfold ofL
  rw [hh_of, dL_of, dL_of, Fin.sum_univ_castSucc, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hh_of, gFace_sn_castSucc]
    rfl
  · rw [gFace_sn_last]
    rfl

theorem d_hh (B : C) (k : ℕ) (y : (L P (k + 1)).obj B) :
    ((dL P (k + 1)).app B).hom (hh B (k + 1) y) = hh B k (((dL P k).app B).hom y) + (-1 : ℤ) ^ (k + 2) • y := by
  have key : AddCommGrpCat.ofHom (((dL P (k + 1)).app B).hom.comp (hh B (k + 1))) =
      AddCommGrpCat.ofHom ((hh B k).comp ((dL P k).app B).hom + (-1 : ℤ) ^ (k + 2) • AddMonoidHom.id ((L P (k + 1)).obj B)) := by
    exact fa_ext fun g => d_hh_of B k g
  exact congrArg (fun f => f.hom y) key

theorem exact_dL (k : ℕ) : (ShortComplex.mk (dL P (k + 1)) (dL P k) (dL_dL k)).Exact := by
  refine exact_of_app _ fun B y => ⟨fun hy => ?_, ?_⟩
  · refine ⟨(-1 : ℤ) ^ (k + 2) • hh B (k + 1) y, ?_⟩
    have e := d_hh B k y
    have hy' : ((dL P k).app B).hom y = 0 := hy
    rw [hy', map_zero, zero_add] at e
    change ((dL P (k + 1)).app B).hom _ = y
    rw [map_zsmul, e, smul_smul, ← mul_pow]
    simp
  · rintro ⟨x, rfl⟩
    exact congrArg (fun f => f.hom x) (congrArg (fun f => f.app B) (dL_dL (P := P) k))

theorem vanish (P : C ⥤ Type) (K : Coef C) (hK : Injective K) (j : ℕ) : Subsingleton (TH P K (j + 1)) :=
  vanish_of_exact exact_dL K hK j

end UpperTheory.Ru.crystallineComparison.Th
end
end

section
theorem UpperTheory.Ru.crystallineComparison.theoryEx :
    UpperTheory.Ru.crystallineComparison.TheoryEx := by
  intro C _
  obtain ⟨z, hz₁, hz₂⟩ := UpperTheory.exists_cohomology_zero_equiv_sections_natural C
  refine ⟨{ H := UpperTheory.Ru.crystallineComparison.Th.TH
            ab := fun _ _ _ => inferInstance
            pull := fun u F j => UpperTheory.Ru.crystallineComparison.Th.tPull u F j
            map := fun P _ _ α j => UpperTheory.Ru.crystallineComparison.Th.tMap P α j
            pull_map := fun u _ _ α j x => UpperTheory.Ru.crystallineComparison.Th.tPull_tMap u α j x
            δ := UpperTheory.Ru.crystallineComparison.Th.tδ
            pull_δ := fun u S h j x => UpperTheory.Ru.crystallineComparison.Th.tPull_tδ u S h j x
            ex₃ := UpperTheory.Ru.crystallineComparison.Th.ex₃
            ex₁ := UpperTheory.Ru.crystallineComparison.Th.ex₁
            zero := z
            zero_pull := hz₁
            zero_map := hz₂
            inj := UpperTheory.Ru.crystallineComparison.Th.vanish }, fun R _ F => ?_⟩
  obtain ⟨F', c, e, h₁, h₂⟩ := UpperTheory.exists_coefficient_equiv_cohomology_of_elements C R F
  exact ⟨F', c, e, h₁, h₂⟩
end
