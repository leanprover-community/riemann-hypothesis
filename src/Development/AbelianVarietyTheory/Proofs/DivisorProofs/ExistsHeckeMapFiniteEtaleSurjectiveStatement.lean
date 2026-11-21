import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapHarrisTaylorIntegralModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLevelForgettingFiniteEtaleSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsFiniteOfCompEtaleSurjective

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_adjoint_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : D.La →ₗ[D.O] D.La) (c k : ℕ),
    c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) →
    c ∣ k ^ 2 → ∃ g' : D.La →ₗ[D.O] D.La, (∀ x, g (g' x) = k • x) ∧ (∀ x, g' (g x) = k • x) ∧
      (∀ x y, D.EF (g' x) (g' y) = (k ^ 2 / c) * D.EF x y) ∧ (∀ x, ∃ y, g' y = k • x) ∧
      (k ^ 2 / c).Coprime p ∧ (k ^ 2 / c) ∣ k ^ 2 ∧ c * (k ^ 2 / c) = k ^ 2 := by
  intro p _ D g c k hc hk hE himg hck
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hp1 (by simpa using hc)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hp1 (by simpa using hk)
  have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast hc0

  have ginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply D.nondeg
    ext y
    have h := hE x y
    rw [hx, map_zero, LinearMap.zero_apply] at h
    simp only [map_zero, LinearMap.zero_apply]
    rcases mul_eq_zero.mp h.symm with h' | h'
    · exact absurd h' hcZ
    · exact h'
  choose f hf using himg
  have fadd : ∀ x y, f (x + y) = f x + f y := fun x y => ginj (by rw [map_add, hf, hf, hf, smul_add])
  have fsmul : ∀ (b : D.O) x, f (b • x) = b • f x := fun b x => ginj (by
    rw [map_smul, hf, hf, smul_comm])
  let g' : D.La →ₗ[D.O] D.La :=
    { toFun := f, map_add' := fadd, map_smul' := fsmul }
  have h1 : ∀ x, g (g' x) = k • x := hf
  have h2 : ∀ x, g' (g x) = k • x := fun x => ginj (by rw [h1, map_nsmul])
  obtain ⟨q, hq⟩ := hck
  have hdiv : k ^ 2 / c = q := by rw [hq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hc0)]
  refine ⟨g', h1, h2, ?_, fun x => ⟨g x, h2 x⟩, ?_, ?_, ?_⟩
  · intro x y
    have h := hE (g' x) (g' y)
    rw [h1, h1, map_nsmul, map_nsmul, LinearMap.smul_apply, smul_smul] at h
    push_cast [hdiv]
    have hqZ : ((k : ℤ) ^ 2 / c) = q := by
      rw [show (k : ℤ) ^ 2 = ((k ^ 2 : ℕ) : ℤ) by push_cast; ring, hq]
      push_cast
      exact Int.mul_ediv_cancel_left _ hcZ
    have hqI : (k : ℤ) ^ 2 = c * q := by exact_mod_cast hq
    rw [hqZ]
    apply mul_left_cancel₀ hcZ
    rw [← h, nsmul_eq_mul]
    push_cast
    rw [← sq, hqI]
    ring
  · rw [hdiv]
    have : q ∣ k ^ 2 := ⟨c, by rw [hq, mul_comm]⟩
    exact Nat.Coprime.coprime_dvd_left this (Nat.Coprime.pow_left 2 hk)
  · rw [hdiv]; exact ⟨c, by rw [hq, mul_comm]⟩
  · rw [hdiv, hq]

end GlobalTheory.UPel.HT.Hecke
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjoint_primeToP_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : D.La →ₗ[D.O] D.La) (c k : ℕ), c.Coprime p → k.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∃ g' : D.La →ₗ[D.O] D.La, (∀ x, g (g' x) = k • x) ∧ (∀ x, g' (g x) = k • x) ∧ (∀ x y, D.EF (g' x) (g' y) = (k ^ 2 / c) * D.EF x y) ∧ (∀ x, ∃ y, g' y = k • x) ∧ (k ^ 2 / c).Coprime p ∧ (k ^ 2 / c) ∣ k ^ 2 ∧ c * (k ^ 2 / c) = k ^ 2 := by
  atlas_forward_decl GlobalTheory.UPel.HT.Hecke.exists_adjoint_similitude
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHeckeTranslate_harrisTaylor_pullback_base : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (o₁ : Obj b (N * k) (f ≫ s)) (o₁' : Obj b N (f ≫ s)), IsHecke g c k N o o' ψ → ObjMap o₁ o f → ObjMap o₁' o' f → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsHecke g c k N o₁ o₁' ψ₁ := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull) | (exact GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_inverse_heckeTranslates_forget_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (o₁ : Obj b (N * k) s) (o₂ : Obj b N s) (ψ₁ : o.A ⟶ o₁.A) (ψ₂ : o₁.A ⟶ o₂.A), IsHecke g' c' k (N * k) o o₁ ψ₁ → IsHecke g c k N o₁ o₂ ψ₂ → Nonempty (ObjMap (o.forget N ⟨k * k, by ring⟩ hc) o₂ (𝟙 S)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget) | (exact GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget) | (intros; apply GlobalTheory.UPel.HT.Hecke.Comp.nonempty_objMap_forget <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem harrisTaylor_heckeMap_comp_forgetLevel_general {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ) (hk : k.Coprime p) (hN3 : 3 ≤ N) (hNp : N.Coprime p)
    (hgg' : ∀ x, g (g' x) = k • x) (hg'g : ∀ x, g' (g x) = k • x) (hcc : c * c' = k ^ 2)
    (hc : (N * k * k).Coprime p)
    {S S₁ S₂ : Scheme.{0}} (s : S ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R)
    (u : Obj b N s) (u₁ : Obj b (N * k) s₁) (u₂ : Obj b (N * k * k) s₂) (π : S₁ ⟶ S) (π₁ : S₂ ⟶ S₁)
    (h₁ : π₁ ≫ s₁ = s₂)
    (o₂ : Obj b N s₁) (ψ₂ : u₁.A ⟶ o₂.A) (hH₂ : IsHecke g c k N u₁ o₂ ψ₂) (m₂ : ObjMap o₂ u π)
    (o₁ : Obj b (N * k) s₂) (ψ₁ : u₂.A ⟶ o₁.A) (hH₁ : IsHecke g' c' k (N * k) u₂ o₁ ψ₁)
    (m₁ : ObjMap o₁ u₁ π₁) :
    Nonempty (ObjMap (u₂.forget N ⟨k * k, by ring⟩ hc) u (π₁ ≫ π)) := by
  subst h₁
  obtain ⟨o₂', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S₁ S₂ s₁ π₁ o₂
  obtain ⟨ψ', hψ'⟩ := GlobalTheory.T.isHeckeTranslate_harrisTaylor_pullback_base p D R b g c k N hk hN3 hNp S₁ S₂ s₁ π₁ u₁ o₂ ψ₂ o₁ o₂' hH₂ m₁ m
  obtain ⟨n⟩ := GlobalTheory.T.harrisTaylor_inverse_heckeTranslates_forget_level p D R b g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc S₂ (π₁ ≫ s₁) u₂ o₁ o₂'
    ψ₁ ψ' hH₁ hψ'
  obtain ⟨n₁⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ n m
  obtain ⟨n₂⟩ := GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ _ _ _ _ _ n₁ m₂
  rw [Category.id_comp] at n₂
  exact ⟨n₂⟩

theorem heckeMap_comp_forget : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (F : RepFam b N) (F₁ : RepFam b (N * k)) (F₂ : RepFam b (N * k * k)) (π : F₁.X ⟶ F.X) (π₁ : F₂.X ⟶ F₁.X), IsHeckeMap g c k N F F₁ π → IsHeckeMap g' c' k (N * k) F₁ F₂ π₁ → Nonempty (ObjMap (F₂.univ.forget N ⟨k * k, by ring⟩ hc) F.univ (π₁ ≫ π)) := by
  intro p _ D R _ b g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc F F₁ F₂ π π₁ hπ hπ₁
  obtain ⟨-, o₂, ψ₂, hH₂, ⟨m₂⟩⟩ := hπ
  obtain ⟨h₁, o₁, ψ₁, hH₁, ⟨m₁⟩⟩ := hπ₁
  exact harrisTaylor_heckeMap_comp_forgetLevel_general g g' c c' k N hk hN3 hNp hgg' hg'g hcc hc F.s F₁.s F₂.s F.univ F₁.univ F₂.univ π π₁ h₁
    o₂ ψ₂ hH₂ m₂ o₁ ψ₁ hH₁ m₁

end GlobalTheory.UPel.HT.Hecke
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_heckeMap_comp_eq_forgetLevel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g g' : D.La →ₗ[D.O] D.La) (c c' k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x, g (g' x) = k • x) → (∀ x, g' (g x) = k • x) → c * c' = k ^ 2 → ∀ (hc : (N * k * k).Coprime p) (F : RepFam b N) (F₁ : RepFam b (N * k)) (F₂ : RepFam b (N * k * k)) (π : F₁.X ⟶ F.X) (π₁ : F₂.X ⟶ F₁.X), IsHeckeMap g c k N F F₁ π → IsHeckeMap g' c' k (N * k) F₁ F₂ π₁ → Nonempty (ObjMap (F₂.univ.forget N ⟨k * k, by ring⟩ hc) F.univ (π₁ ≫ π)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.heckeMap_comp_forget) | (exact GlobalTheory.UPel.HT.Hecke.heckeMap_comp_forget) | (intros; apply GlobalTheory.UPel.HT.Hecke.heckeMap_comp_forget <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory

theorem etale_of_comp_etale_of_smoothOfRelativeDimension :
    ∀ (X Y Z S : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z) (sX : X ⟶ S) (sY : Y ⟶ S) (d : ℕ),
      h ≫ sY = sX → SmoothOfRelativeDimension d sX → SmoothOfRelativeDimension d sY →
      Etale (h ≫ f) → Etale h := by
  intro X Y Z S h f sX sY d hs hX hY he
  subst hs
  haveI : FormallyUnramified (h ≫ f) := inferInstance
  haveI : FormallyUnramified h := FormallyUnramified.of_comp h f
  exact etale_of_formallyUnramified_of_smoothOfRelativeDimension h sY d hY hX

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_comp_etale_sameRelativeDimension : ∀ (X Y Z S : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z) (sX : X ⟶ S) (sY : Y ⟶ S) (d : ℕ), h ≫ sY = sX → SmoothOfRelativeDimension d sX → SmoothOfRelativeDimension d sY → Etale (h ≫ f) → Etale h := by
  first | (exact @GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension) | (exact GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension) | (intros; apply GlobalTheory.etale_of_comp_etale_of_smoothOfRelativeDimension  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_isFinite_of_comp_etale_surjective' : ∀ (X Y Z : Scheme.{0}) (h : X ⟶ Y) (f : Y ⟶ Z), Etale h → Surjective h → Etale (h ≫ f) → IsFinite (h ≫ f) → IsSeparated f → LocallyOfFiniteType f → Etale f ∧ IsFinite f := by
  first | (exact @GlobalTheory.etale_isFinite_of_comp_etale_surjective) | (exact GlobalTheory.etale_isFinite_of_comp_etale_surjective) | (intros; apply GlobalTheory.etale_isFinite_of_comp_etale_surjective <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem isSeparated_model_str {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) : IsSeparated M.s := by
  obtain ⟨n, i, hi, -, e⟩ := M.qproj
  have : IsSeparated (PSpace.str R n) := by
    unfold PSpace.str
    infer_instance
  rw [← e]
  infer_instance

theorem exists_heckeMap_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π ∧ IsFinite π ∧ Etale π ∧ Surjective π := by
  intro p _ D R _ _ b g c k N hc hk hN hNp hg hgk hck M M'
  have hp : p.Prime := Fact.out
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      exact absurd (Nat.coprime_zero_left p |>.1 hk) hp.ne_one
    · exact h
  obtain ⟨g', h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.exists_adjoint_primeToP_similitude p D g c k hc hk hg hgk hck
  have h3' : ∀ x y, D.EF (g' x) (g' y) = ((k ^ 2 / c : ℕ) : ℤ) * D.EF x y := by
    intro x y
    rw [h3 x y]
    push_cast
    rfl
  have c1 : (N * k).Coprime p := Nat.Coprime.mul_left hNp hk
  have c2 : (N * k * k).Coprime p := Nat.Coprime.mul_left c1 hk
  have c3 : (N * k * k * k).Coprime p := Nat.Coprime.mul_left c2 hk
  have l1 : 3 ≤ N * k := hN.trans (Nat.le_mul_of_pos_right _ hk0)
  have l2 : 3 ≤ N * k * k := l1.trans (Nat.le_mul_of_pos_right _ hk0)
  have l3 : 3 ≤ N * k * k * k := l2.trans (Nat.le_mul_of_pos_right _ hk0)
  obtain ⟨M₂⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R b (N * k * k) l2 c2
  obtain ⟨M₃⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R b (N * k * k * k) l3 c3
  obtain ⟨π, hπ⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g c k N hc hk hN hNp hg hgk hck M M'
  obtain ⟨π₁, hπ₁⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g' (k ^ 2 / c) k (N * k) h5 hk l1 c1 h3' h4 h6 M' M₂
  obtain ⟨π₂, hπ₂⟩ := GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels p D R b g c k (N * k * k) hc hk l2 c2 hg hgk hck M₂ M₃
  have e : π ≫ M.s = M'.s := hπ.1
  have e₁ : π₁ ≫ M'.s = M₂.s := hπ₁.1
  have e₂ : π₂ ≫ M₂.s = M₃.s := hπ₂.1
  have f1 := GlobalTheory.T.harrisTaylor_heckeMap_comp_eq_forgetLevel p D R b g g' c (k ^ 2 / c) k N hk hN hNp h1 h2 h7 c2 M.toRepFam M'.toRepFam
    M₂.toRepFam π π₁ hπ hπ₁
  have f2 := GlobalTheory.T.harrisTaylor_heckeMap_comp_eq_forgetLevel p D R b g' g (k ^ 2 / c) c k (N * k) hk l1 c1 h2 h1 (by rw [mul_comm, h7]) c3
    M'.toRepFam M₂.toRepFam M₃.toRepFam π₁ π₂ hπ₁ hπ₂
  obtain ⟨a1, a2, a3⟩ := GlobalTheory.T.harrisTaylor_levelForgetting_finite_etale_surjective p D R b N (N * k * k) _ c2 hN M M₂ (π₁ ≫ π)
    (by rw [Category.assoc, e, e₁]) f1
  obtain ⟨-, -, b3⟩ := GlobalTheory.T.harrisTaylor_levelForgetting_finite_etale_surjective p D R b (N * k) (N * k * k * k) _ c3 l1 M' M₃ (π₂ ≫ π₁)
    (by rw [Category.assoc, e₁, e₂]) f2
  have s1 : Surjective π₁ := Surjective.of_comp π₂ π₁
  have t1 : Etale π₁ := GlobalTheory.T.etale_of_comp_etale_sameRelativeDimension _ _ _ _ π₁ π M₂.s M'.s _ e₁ M₂.smooth M'.smooth a2
  have hs : IsSeparated π := by
    have : IsSeparated (π ≫ M.s) := e ▸ isSeparated_model_str M'
    exact IsSeparated.of_comp π M.s
  have hl : LocallyOfFiniteType π := by
    have := M'.smooth
    have : Smooth M'.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M'.s
    have : LocallyOfFiniteType (π ≫ M.s) := by rw [e]; infer_instance
    exact locallyOfFiniteType_of_comp π M.s
  obtain ⟨r1, r2⟩ := GlobalTheory.T.etale_isFinite_of_comp_etale_surjective' _ _ _ π₁ π t1 s1 a2 a1 hs hl
  exact ⟨π, hπ, r2, r1, Surjective.of_comp π₁ π⟩

end GlobalTheory.UPel.HT.Hecke
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeMap_finite_etale_surjective' : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π ∧ IsFinite π ∧ Etale π ∧ Surjective π := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_heckeMap_finite_etale_surjective) | (exact GlobalTheory.UPel.HT.Hecke.exists_heckeMap_finite_etale_surjective) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_heckeMap_finite_etale_surjective  <;> assumption)
end
