import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
import Development.EtaleCohomology.KummerTheory.DictNormalPf
import Development.EtaleCohomology.TateTwists.EtaleChainCochainExistsOfEvalData
import Development.EtaleCohomology.KummerTheory.CupAWCutEv

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.DiscPf

variable {R : Type} [CommRing R]

abbrev Cd (R : Type) [CommRing R] (P : PSh) : Cx R := (chains R).obj (disc.obj P)

abbrev e0 (R : Type) [CommRing R] (P : PSh) : (Cd R P).X (-((0 : ℕ) : ℤ)) ≅ (free R).obj P := chainsXIso R (disc.obj P) 0

theorem isZero_pos (P : PSh) (j : ℤ) (hj : 0 < j) : IsZero ((Cd R P).X j) :=
  HomologicalComplex.isZero_extend_X ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat j
    (fun i h => by change (-(i : ℤ)) = j at h; omega)

theorem d_one (P : PSh) : (Cd R P).d (-1) (-((0 : ℕ) : ℤ)) = 0 := by
  have h := LateralTheory.KummerTheory.chains_d R (disc.obj P) 0
  have hs : (∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ (disc.obj P) i)) = 0 := by
    have : ∀ i : Fin (0 + 2), (free R).map (SimplicialObject.δ (disc.obj P) i) = 𝟙 _ := fun i => (free R).map_id _
    simp only [this]
    simp
  rw [hs, zero_comp] at h
  have : (chainsXIso R (disc.obj P) (0 + 1)).hom ≫ (chainsXIso R (disc.obj P) (0 + 1)).inv ≫
      (Cd R P).d (-((0 + 1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) = 0 := by rw [h, comp_zero]
  simpa using this

def coch {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) : Cochain (Cd R P) K n :=
  Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((e0 R P).hom ≫ a) n

theorem coch_add {K : Cx R} {n : ℤ} (P : PSh) (a b : (free R).obj P ⟶ K.X n) : coch P (a + b) = coch P a + coch P b := by
  ext p q hpq
  by_cases hp : p = -((0 : ℕ) : ℤ)
  · subst hp
    obtain rfl : q = n := by omega
    simp [coch, Cochain.single_v]
  · simp [coch, Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem delta_coch {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) :
    δ n (n + 1) (coch P a) = Cochain.single (p := -((0 : ℕ) : ℤ)) ((e0 R P).hom ≫ a ≫ K.d n (n + 1)) (n + 1) := by
  rw [coch, Cochain.δ_single _ n (n + 1) rfl (-1) (n + 1) (by simp) rfl, d_one, zero_comp, Cochain.single_zero, smul_zero,
    add_zero, Category.assoc]

theorem coch_cocycle {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    δ n (n + 1) (coch P a) = 0 := by
  rw [delta_coch, ha, comp_zero, Cochain.single_zero]

def cz {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) : Cocycle (Cd R P) K n :=
  ⟨coch P a, (Cocycle.mem_iff n (n + 1) rfl _).2 (coch_cocycle P a ha)⟩

open Classical in
def cl (K : Cx R) (n : ℤ) (P : PSh) (a : (free R).obj P ⟶ K.X n) : CohomologyClass (Cd R P) K n :=
  if ha : a ≫ K.d n (n + 1) = 0 then CohomologyClass.mk (cz P a ha) else 0

theorem cl_eq {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cl K n P a = CohomologyClass.mk (cz P a ha) := dif_pos ha

theorem cl_add {K : Cx R} {n : ℤ} (P : PSh) (a b : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0)
    (hb : b ≫ K.d n (n + 1) = 0) : cl K n P (a + b) = cl K n P a + cl K n P b := by
  have hab : (a + b) ≫ K.d n (n + 1) = 0 := by rw [Preadditive.add_comp, ha, hb, add_zero]
  rw [cl_eq _ _ ha, cl_eq _ _ hb, cl_eq _ _ hab, ← CohomologyClass.mk_add]
  congr 1
  exact Cocycle.ext (coch_add P a b)

theorem cl_zero_iff {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cl K n P a = 0 ↔ ∃ b, b ≫ K.d (n - 1) n = a := by
  rw [cl_eq _ _ ha, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨(e0 R P).inv ≫ β.v (-((0 : ℕ) : ℤ)) (n - 1) (by omega), ?_⟩
    have h1 := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) n (by omega)
    rw [δ_v (n - 1) n (by omega) β _ n _ (n - 1) (-((0 : ℕ) : ℤ) + 1) (by omega) rfl,
      (isZero_pos P (-((0 : ℕ) : ℤ) + 1) (by omega)).eq_of_tgt ((Cd R P).d (-((0 : ℕ) : ℤ)) _) 0, zero_comp, smul_zero, add_zero] at h1
    have h2 : (cz P a ha).1.v (-((0 : ℕ) : ℤ)) n (by omega) = (e0 R P).hom ≫ a := Cochain.single_v _ _ _
    rw [h2] at h1
    rw [Category.assoc, h1, Iso.inv_hom_id_assoc]
  · rintro ⟨b, rfl⟩
    refine ⟨Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n - 1) ((e0 R P).hom ≫ b) (n - 1), ?_⟩
    rw [Cochain.δ_single _ (n - 1) n (by omega) (-1) n (by simp) (by omega), d_one, zero_comp, Cochain.single_zero, smul_zero,
      add_zero, Category.assoc]
    rfl

theorem etale_discrete_chains_degree_zero_iso_free_naturality (P' P : PSh) (f : P' ⟶ P) :
    ((chains R).map (disc.map f)).f (-((0 : ℕ) : ℤ)) ≫ (e0 R P).hom = (e0 R P').hom ≫ (free R).map f := by
  dsimp only [chains, e0, chainsXIso, Functor.comp_map, Functor.comp_obj]
  erw [HomologicalComplex.extendMap_f _ _ (i := 0) rfl]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem cl_nat {K : Cx R} {n : ℤ} (P' P : PSh) (f : P' ⟶ P) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cpre (Cocycle.ofHom ((chains R).map (disc.map f))) K n n (zero_add n) (cl K n P a) = cl K n P' ((free R).map f ≫ a) := by
  have ha' : ((free R).map f ≫ a) ≫ K.d n (n + 1) = 0 := by rw [Category.assoc, ha, comp_zero]
  rw [cl_eq _ _ ha, cl_eq _ _ ha', cpre_mk]
  congr 1
  apply Cocycle.ext
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  change ((Cochain.ofHom ((chains R).map (disc.map f))).comp (coch P a) (zero_add n)).v p q hpq = (coch P' _).v p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  by_cases hp : p = -((0 : ℕ) : ℤ)
  · subst hp
    obtain rfl : q = n := by omega
    simp only [coch, Cochain.single_v]
    rw [← Category.assoc, etale_discrete_chains_degree_zero_iso_free_naturality, Category.assoc]
  · simp only [coch, Cochain.single_v_eq_zero _ _ _ _ _ hp, comp_zero]

end LateralTheory.CohomologicalPurity.Cl.DiscPf

namespace LateralTheory.CohomologicalPurity.Cl

open DiscPf in

def LeafDiscNrm : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ) (P : PSh)
  (z : Cocycle ((chains R).obj (disc.obj P)) K n),
  ∃ (a : (free R).obj P ⟶ K.X n) (β : Cochain ((chains R).obj (disc.obj P)) K (n - 1)),
    z.1 = Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((chainsXIso R (disc.obj P) 0).hom ≫ a) n + δ (n - 1) n β

open DiscPf in
theorem LeafDisc_of (hN : LeafDiscNrm) : LeafDisc := by
  intro R _ K n
  refine ⟨cl K n, fun P a b ha hb => cl_add P a b ha hb, ?_, fun P a ha => cl_zero_iff P a ha,
    fun P' P f a ha => cl_nat P' P f a ha⟩
  intro P x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨a, β, hz⟩ := hN R K n P z
  have hz0 : δ n (n + 1) z.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl z.1).1 z.2
  have hc : δ n (n + 1) (coch P a) = 0 := by
    have := hz0
    rw [hz, δ_add, δ_δ, add_zero] at this
    exact this
  have ha : a ≫ K.d n (n + 1) = 0 := by
    rw [delta_coch] at hc
    have h1 := Cochain.congr_v hc (-((0 : ℕ) : ℤ)) (n + 1) (by omega)
    rw [Cochain.single_v, Cochain.zero_v] at h1
    exact (cancel_epi (e0 R P).hom).1 (h1.trans (comp_zero).symm)
  refine ⟨a, ha, ?_⟩
  rw [cl_eq _ _ ha, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨-β, ?_⟩
  rw [δ_neg]
  change _ = coch P a - z.1
  rw [hz]
  unfold coch
  abel

end LateralTheory.CohomologicalPurity.Cl
end
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl.DiscNrmPf

def up {P : PSh} {U : Scheme.{0}} {p q : ℕ} (x : Sx (disc.obj P) p U) : Sx (disc.obj P) q U := x

theorem face_disc {P : PSh} {U : Scheme.{0}} {p : ℕ} (x : Sx (disc.obj P) (p + 1) U) (i : Fin (p + 2)) :
    ((disc.obj P).δ i).app (op U) x = up x := rfl

theorem normal (R : Type) [CommRing R] (I : Cx R) (P : PSh) (n : ℤ) (α : Cocycle ((chains R).obj (disc.obj P)) I n) :
    ∃ β : Cochain ((chains R).obj (disc.obj P)) I (n - 1), ∀ p s h U y,
      ev (α.1 - δ (n - 1) n β) (p + 1) s h U y = 0 := by
  have hα : δ n (n + 1) α.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2
  have hD := LateralTheory.KummerTheory.nrmDelta
  obtain ⟨β, hβ⟩ := LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data R (E := disc.obj P) (I := I) (n := n - 1)
    (fun p s h U x => if Odd p then n.negOnePow • ev α.1 (p + 1) s (by push_cast; omega) U (up x) else 0)
    (by
      intro p s h V U g x
      beta_reduce
      split_ifs
      · rw [Units.smul_def, Units.smul_def]
        refine (map_zsmul ((I.X s).obj.map g.op).hom _ _).trans ?_
        exact congrArg (fun v => (n.negOnePow : ℤ) • v) (LateralTheory.KummerTheory.AW.ev_res α.1 (p + 1) s _ g (up x))
      · exact map_zero _)
  refine ⟨β, ?_⟩
  intro p s h U y
  rw [LateralTheory.KummerTheory.ev_sub', sub_eq_zero]
  rw [hD R (by omega) β U p (s - 1) s (by push_cast at h ⊢; omega) h y]
  simp only [face_disc, hβ]
  rcases Nat.even_or_odd p with hp | hp
  · have hp1 : Odd (p + 1) := hp.add_one
    have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
    simp only [hp1, hp0, if_true, if_false, smul_zero, Finset.sum_const_zero, add_zero]
    have hc := hD R (n := n) (m := n + 1) rfl α.1 U (p + 1) (s - 1) s (by push_cast at h ⊢; omega)
      (by push_cast at h ⊢; omega) (up y)
    rw [hα, LateralTheory.KummerTheory.ev_zero'] at hc
    simp only [face_disc] at hc
    rw [← Finset.sum_smul, LateralTheory.KummerTheory.altsum] at hc
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
    rw [← Finset.sum_smul, LateralTheory.KummerTheory.altsum]
    have he : ¬ Even (p + 2) := by
      rw [Nat.not_even_iff_odd]; exact hp.add_even even_two
    simp only [he, if_false, one_smul, smul_smul, Int.units_mul_self]
    rfl

end LateralTheory.CohomologicalPurity.Cl.DiscNrmPf

namespace LateralTheory.CohomologicalPurity.Cl

open DiscNrmPf in
theorem etale_discrete_presheaf_cocycle_normalization_holds : LeafDiscNrm := by
  intro R _ K n P z
  obtain ⟨β, hβ⟩ := normal R K P n z
  refine ⟨(chainsXIso R (disc.obj P) 0).inv ≫ (z.1 - δ (n - 1) n β).v (-((0 : ℕ) : ℤ)) n (by omega), β, ?_⟩
  rw [← sub_eq_iff_eq_add]
  apply LateralTheory.KummerTheory.AW.ev_ext
  intro p s h U x
  rcases p with _ | p
  · obtain rfl : s = n := by omega
    simp only [ev, Cochain.single_v, Iso.inv_hom_id_assoc]
  · rw [hβ]
    simp only [ev]
    rw [Cochain.single_v_eq_zero _ _ _ _ _ (by push_cast; omega), comp_zero]
    rfl

theorem LeafDisc_of' : LeafDisc := LeafDisc_of etale_discrete_presheaf_cocycle_normalization_holds

end LateralTheory.CohomologicalPurity.Cl
end
end
