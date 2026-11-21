import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsPullSnd

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

section GV

variable {X Y Y' : Scheme.{0}} (M : LB X)

def GV (F : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U)
    (v : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : (Z ⟶ X) → M.ι), (Z.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb M φ ε)), u.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ Z r z J, Good M z J → val u r z J = v Z r z J

variable {M} {F F' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} {v v'}

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  first
    | (rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl)
    | (rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
    | simp [← Functor.map_comp_apply]
    | simp

private lemma isGen_mulGen_of_isGen {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen) (ht' : t'.IsGen) :
    (LB.mulGen L φ ε φ' ε' t t').IsGen := by
  intro j j'
  have hl : ∀ i : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') i ≤ LB.wchart L φ (i ∘ Sum.inl) :=
    fun i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have hr : ∀ i : K ⊕ K' → L.ι, LB.wchart L (Sum.elim φ φ') i ≤ LB.wchart L φ' (i ∘ Sum.inr) :=
    fun i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  have e1 := congrArg (res (inf_le_inf (hl j) (hl j'))) (ht (j ∘ Sum.inl) (j' ∘ Sum.inl))
  have e2 := congrArg (res (inf_le_inf (hr j) (hr j'))) (ht' (j ∘ Sum.inr) (j' ∘ Sum.inr))
  erw [map_mul, res_res_lemma, res_res_lemma] at e1
  erw [map_mul, res_res_lemma, res_res_lemma] at e2
  have hg : (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')).g j j' =
      res (inf_le_inf (hl j) (hl j')) ((LB.LinComb L φ ε).g (j ∘ Sum.inl) (j' ∘ Sum.inl)) *
        res (inf_le_inf (hr j) (hr j')) ((LB.LinComb L φ' ε').g (j ∘ Sum.inr) (j' ∘ Sum.inr)) := by
    dsimp only [LB.LinComb]
    rw [Fintype.prod_sum_type]
    erw [map_prod, map_prod]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_) <;>
      erw [map_zpow, res_res_lemma] <;> rfl
  dsimp only [LB.mulGen]
  erw [map_mul, map_mul, res_res_lemma, res_res_lemma, res_res_lemma, res_res_lemma, e1, e2, hg]
  exact mul_mul_mul_comm _ _ _ _

private lemma isGen_invGen_of_isGen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    (LB.invGen L φ ε t).IsGen := by
  intro i i'
  have hg : (LB.LinComb L φ fun k => -ε k).g i i' = ((LB.LinComb L φ ε).g i i')⁻¹ := by
    dsimp only [LB.LinComb]
    simp only [zpow_neg, Finset.prod_inv_distrib] <;> rfl
  dsimp only [LB.invGen]
  erw [map_inv, map_inv, ht i i', mul_inv, hg]
  rfl

private lemma pullU_comp_toroidal_compactification {X Y Z : Scheme.{0}} (h : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (h ≫ f) U x = pullU h (f ⁻¹ᵁ U) (pullU f U x) := by
  first
    | rfl
    | (ext; rfl)
    | (ext; simp [pullU])

private lemma pullU_res_toroidal_compactification {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (p : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res p x) = res (fun _ hy => p hy : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (pullU f U x) := by
  ext
  simp only [pullU, res, Units.coe_map, MonoidHom.coe_coe]
  first
    | exact congrArg (fun g => g.hom x.1) (f.naturality (homOfLE p).op)
    | exact (congrArg (fun g => g.hom x.1) (f.naturality (homOfLE p).op)).symm
    | (rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]; rfl)
    | simp [← CommRingCat.comp_apply, Scheme.Hom.naturality]

private lemma res_pullU_comp_eq_res_pullU_res_pullU {X Y Z : Scheme.{0}} (h : Z ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    {W : Z.Opens} (p : V ≤ f ⁻¹ᵁ U) (hB : W ≤ h ⁻¹ᵁ V) (q : W ≤ (h ≫ f) ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res q (pullU (h ≫ f) U x) = res hB (pullU h V (res p (pullU f U x))) := by
  rw [pullU_res_toroidal_compactification]
  erw [res_res_lemma]
  first
    | done
    | rfl
    | (erw [pullU_comp_toroidal_compactification]; done)
    | (erw [pullU_comp_toroidal_compactification]; rfl)

set_option maxHeartbeats 800000 in

private lemma isGen_pullGen_of_isGen {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) (h : Z ⟶ Y) :
    (LB.pullGen L φ ε c h).IsGen := by
  intro j j'
  have hP : ∀ i : K → L.ι, LB.wchart L (fun k => h ≫ φ k) i ≤ h ⁻¹ᵁ LB.wchart L φ i :=
    fun i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hB : LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ k) j' ≤
      h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := by
    first
      | exact fun x hy => ⟨hP j hy.1, hP j' hy.2⟩
      | exact fun x hy => ⟨hP j (Opens.mem_inf.1 hy).1, hP j' (Opens.mem_inf.1 hy).2⟩
      | exact fun x hy => by simp only [Opens.mem_inf] at hy ⊢; exact ⟨hP j hy.1, hP j' hy.2⟩
  have e := congrArg (fun x => res hB (pullU h (LB.wchart L φ j ⊓ LB.wchart L φ j') x)) (hc j j')
  try dsimp only at e
  erw [map_mul, map_mul, pullU_res_toroidal_compactification, pullU_res_toroidal_compactification, res_res_lemma, res_res_lemma] at e
  have hg : (LB.LinComb L (fun k => h ≫ φ k) ε).g j j' =
      res hB (pullU h (LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j')) := by
    dsimp only [LB.LinComb]
    erw [map_prod, map_prod]
    congr 1
    funext k
    erw [map_zpow, map_zpow]
    congr 1
    exact res_pullU_comp_eq_res_pullU_res_pullU (U := L.U (j k) ⊓ L.U (j' k)) h (φ k) _ hB _ (L.g (j k) (j' k))
  dsimp only [LB.pullGen]
  erw [res_res_lemma, res_res_lemma, e, hg]
  rfl

theorem GV.mul (a : GV M F v) (b : GV M F' v') :
    GV M (fun U _ h => F U h * F' U h) fun Z r z J => v Z r z J * v' Z r z J := by
  obtain ⟨K, hK, φ, ε, u, hu, hF, hv⟩ := a
  obtain ⟨K', hK', φ', ε', u', hu', hF', hv'⟩ := b
  refine ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', LB.mulGen (L := M) φ ε φ' ε' u u',
    isGen_mulGen_of_isGen M φ ε φ' ε' u u' hu hu', ?_, ?_⟩
  · intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hF, hF']
  · intro Z r z J hJ
    rw [val_mul, hv Z r z J hJ, hv' Z r z J hJ]
    all_goals first | assumption | exact hJ

theorem GV.inv (a : GV M F v) : GV M (fun U _ h => (F U h)⁻¹) fun Z r z J => (v Z r z J)⁻¹ := by
  obtain ⟨K, hK, φ, ε, u, hu, hF, hv⟩ := a
  refine ⟨K, hK, φ, fun k => -ε k, LB.invGen (L := M) φ ε u, isGen_invGen_of_isGen M φ ε u hu, ?_, ?_⟩
  · intro U _ h
    simp only [zpow_neg, Finset.prod_inv_distrib, hF]
  · intro Z r z J hJ
    rw [val_inv, hv Z r z J hJ]
    all_goals first | assumption | exact hJ

theorem GV.pull (a : GV M F v) (g : Y' ⟶ Y) : GV M (fun U _ h => F U fun q => h (g ≫ q)) fun Z r z J => v Z (r ≫ g) z J := by
  obtain ⟨K, hK, φ, ε, u, hu, hF, hv⟩ := a
  refine ⟨K, hK, fun k => g ≫ φ k, ε, LB.pullGen (L := M) φ ε u g, isGen_pullGen_of_isGen M φ ε u hu g, ?_, ?_⟩
  · intro U _ h
    exact hF U fun q => h (g ≫ q)
  · intro Z r z J hJ
    rw [val_pull]
    · exact hv Z (r ≫ g) z J hJ
    all_goals first | assumption | exact hJ

theorem GV.pow (a : GV M F v) (n : ℕ) : GV M (fun U _ h => F U h ^ n) fun Z r z J => v Z r z J ^ n := by
  have key : ∀ {G G' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U}
      {w w' : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z) (_ : (Z ⟶ X) → M.ι), (Z.presheaf.stalk z)ˣ},
      GV M G w → G = G' → w = w' → GV M G' w' := by
    intro G G' w w' h hG hw
    subst hG
    subst hw
    exact h
  induction n with
  | zero =>
    refine key (a.mul a.inv) ?_ ?_
    · funext U inst h
      exact (mul_inv_cancel _).trans (pow_zero _).symm
    · funext Z r z J
      exact (mul_inv_cancel _).trans (pow_zero _).symm
  | succ n ih =>
    refine key (ih.mul a) ?_ ?_
    · funext U inst h
      exact (pow_succ _ _).symm
    · funext Z r z J
      exact (pow_succ _ _).symm

end GV


variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (hG : GlobalFnsSt)
  (hA : IsAbelianScheme A)
include c hG hA



end ReciprocityTheory.ChartRestriction.G.Geo.Tor
