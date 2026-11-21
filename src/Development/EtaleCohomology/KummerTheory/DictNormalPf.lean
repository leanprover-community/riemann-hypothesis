import Development.EtaleCohomology.KummerTheory.DictPf

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem ev_add (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  simp [ev, Cochain.add_v, Preadditive.comp_add]

theorem ev_neg (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) p s h U x :
    ev (-α) p s h U x = -ev α p s h U x := by
  have h0 : ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by simp [ev]
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← ev_add, neg_add_cancel, h0]

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem val_res' (R : Type) [CommRing R] {P : PSh} {F : Shv R} (φ : (free R).obj P ⟶ F) (V U : Scheme.{0}) (g : V ⟶ U)
    (x : P.obj (op U)) :
    Sec.res g ((φ.hom.app (op U)).hom (freeGen R P U x)) = (φ.hom.app (op V)).hom (freeGen R P V (P.map g.op x)) := by
  have e1 := congrArg (fun (f : ((free R).obj P).obj.obj (op U) ⟶ F.obj.obj (op V)) => f.hom (freeGen R P U x)) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1
  refine e1.symm.trans (congrArg _ ?_)
  have e2 := congrArg (fun (f : ((freeP R).obj P).obj (op U) ⟶ ((free R).obj P).obj.obj (op V)) => f.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  erw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at e2
  unfold freeGen
  refine e2.symm.trans (congrArg _ ?_)
  first
  | rfl
  | exact Finsupp.mapDomain_single
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem ev_res (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) :=
  val_res' R _ V U g x

theorem free_gen_map (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  have e := congrArg (fun (φ : ((freeP R).obj P).obj (op U) ⟶ ((free R).obj Q).obj.obj (op U)) =>
    φ.hom (ModuleCat.freeMk (ULift.up x))) (congrArg (fun η => η.app (op U)) (toSheafify_naturality Scheme.etaleTopology ((freeP R).map f)))
  erw [NatTrans.comp_app, NatTrans.comp_app, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    LinearMap.comp_apply] at e
  unfold freeGen
  refine e.symm.trans (congrArg _ ?_)
  first
  | rfl
  | exact Finsupp.mapDomain_single

theorem chainsXIso_nat (R : Type) [CommRing R] {E' E : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p : ℤ)) = (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  simp only [chainsXIso, chains, chainsN, Functor.comp_map, ComplexShape.embeddingDownNat, Functor.comp_obj]
  erw [HomologicalComplex.extendMap_f _ _ (i := p) rfl]
  simp only [AlgebraicTopology.alternatingFaceMapComplex_map_f, SimplicialObject.whiskering_obj_map_app]
  erw [Iso.inv_hom_id_assoc]
  rfl
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory
theorem ev_pre (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} {E' : Spc} (f : E' ⟶ E)
    (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  unfold ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainsXIso_nat, Category.assoc]
  exact congrArg (fun y => (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op U)).hom y) (free_gen_map R _ U x)

theorem evLin : EvLin := fun R _ E I n =>
  ⟨fun α β p s h U x => ⟨ev_add R α β p s h U x, ev_neg R α p s h U x⟩,
   fun α p s h V U g x => ev_res R α p s h V U g x,
   fun f α p s h U x => ev_pre R f α p s h U x⟩
end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem Dict_of' (hE : DictExist) (hN : DictNormal) (hZ : DictZero) : Dict := Dict_of evLin hE hN hZ
end LateralTheory.KummerTheory
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def NrmMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
    Sec.res g (a p s h U x) = a p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def NrmDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (_hm : n + 1 = m)
  (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
  (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
  ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
    m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U ((E.δ i).app (op U) x)

def up {X U : Scheme.{0}} {p q : ℕ} (x : Sx (sch.obj X) p U) : Sx (sch.obj X) q U := x

theorem face_sch {X U : Scheme.{0}} {p : ℕ} (x : Sx (sch.obj X) (p + 1) U) (i : Fin (p + 2)) :
    ((sch.obj X).δ i).app (op U) x = up x := rfl

theorem altsum (k : ℕ) : ∑ i : Fin k, (-1 : ℤ) ^ (i : ℕ) = if Even k then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · have : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hk
      simp [hk, this, hk.neg_one_pow]
    · have : Even (k + 1) := hk.add_one
      have h2 : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      simp [h2, this, hk.neg_one_pow]

theorem ev_zero' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} p s h U x :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by simp [ev]

theorem ev_sub' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  rw [sub_eq_add_neg, ev_add, ev_neg, ← sub_eq_add_neg]

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem DictNormal_of (hM : NrmMk) (hD : NrmDelta) : DictNormal := by
  intro R _ I X n α
  have hα : δ n (n + 1) α.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2
  obtain ⟨β, hβ⟩ := hM R (E := sch.obj X) (I := I) (n := n - 1)
    (fun p s h U x => if Odd p then n.negOnePow • ev α.1 (p + 1) s (by push_cast; omega) U (up x) else 0)
    (by
      intro p s h V U g x
      dsimp only
      split_ifs
      · rw [Units.smul_def, Units.smul_def]
        refine (map_zsmul ((I.X s).obj.map g.op).hom _ _).trans ?_
        exact congrArg (fun v => (n.negOnePow : ℤ) • v) (ev_res R α.1 (p + 1) s _ V U g (up x))
      · exact map_zero _)
  let γ : Cocycle ((chains R).obj (sch.obj X)) I n :=
    ⟨δ (n - 1) n β, (Cocycle.mem_iff n (n + 1) rfl _).2 (δ_δ _ _ _ _)⟩
  refine ⟨α - γ, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff γ (n - 1) (by omega)]
    exact ⟨β, rfl⟩
  · intro p s h U y
    show ev (α.1 - δ (n - 1) n β) (p + 1) s h U y = 0
    rw [ev_sub', sub_eq_zero]
    rw [hD R (by omega) β U p (s - 1) s (by push_cast at h ⊢; omega) h y]
    simp only [face_sch, hβ]
    rcases Nat.even_or_odd p with hp | hp
    ·
      have hp1 : Odd (p + 1) := hp.add_one
      have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
      simp only [hp1, hp0, if_true, if_false, smul_zero, Finset.sum_const_zero, add_zero]
      have hc := hD R (n := n) (m := n + 1) rfl α.1 U (p + 1) (s - 1) s (by push_cast at h ⊢; omega)
        (by push_cast at h ⊢; omega) (up y)
      rw [hα, ev_zero'] at hc
      simp only [face_sch] at hc
      rw [← Finset.sum_smul, altsum] at hc
      have he : ¬ Even (p + 1 + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp1.add_even even_two
      simp only [he, if_false, one_smul] at hc
      rw [Int.negOnePow_succ, Units.neg_smul] at hc
      have key := add_neg_eq_zero.1 hc.symm
      rw [Units.smul_def]
      refine Eq.trans ?_ (map_zsmul ((I.d (s - 1) s).hom.app (op U)).hom _ _).symm
      rw [show (ModuleCat.Hom.hom ((I.d (s - 1) s).hom.app (op U))) (ev α.1 (p + 1 + 1) (s - 1) (by push_cast at h ⊢; omega) U (up y))
          = n.negOnePow • ev α.1 (p + 1) s (by push_cast at h ⊢; omega) U (up (up y)) from key]
      rw [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
      rfl
    · have hp1 : ¬ Odd (p + 1) := Nat.not_odd_iff_even.mpr hp.add_one
      simp only [hp1, hp, if_true, if_false, map_zero, zero_add]
      rw [← Finset.sum_smul, altsum]
      have he : ¬ Even (p + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp.add_even even_two
      simp only [he, if_false, one_smul, smul_smul, Int.units_mul_self]
      rfl

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem chains_d (R : Type) [CommRing R] (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  simp only [chainsXIso, chains, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq _ _ (i := p + 1) (j := p) rfl rfl]
  erw [Iso.inv_hom_id_assoc]
  congr 1
  simp only [chainsN, Functor.comp_obj]
  erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  rfl

def evAt {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) : (F ⟶ G) →+ Sec G U where
  toFun φ := (φ.hom.app (op U)).hom y
  map_zero' := by simp
  map_add' := by simp

theorem evAt_apply {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) (φ : F ⟶ G) :
    evAt U y φ = (φ.hom.app (op U)).hom y := rfl

theorem nrmDelta : NrmDelta := by
  intro R _ E I n m hm α U p s t hs ht x
  unfold ev
  rw [δ_v n m hm α (-((p + 1 : ℕ) : ℤ)) t ht s (-(p : ℤ)) (by omega) (by push_cast; omega)]
  rw [Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _),
    chains_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  simp [Units.smul_def, Finset.smul_sum]
  refine (map_sum (evAt (G := I.X t) U (freeGen R (E.obj (op (SimplexCategory.mk (p + 1)))) U x)) _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 2
  have := free_gen_map R (E.δ i) U x
  rw [evAt_apply]
  simp
  exact congrArg (fun z => (ModuleCat.Hom.hom ((α.v (-(p : ℤ)) t (by push_cast at ht ⊢; omega)).hom.app (op U)))
    ((ModuleCat.Hom.hom ((chainsXIso R E p).inv.hom.app (op U))) z)) this

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem DictNormal_of' (hM : NrmMk) : DictNormal := DictNormal_of hM nrmDelta
end LateralTheory.KummerTheory
end
end
