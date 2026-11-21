import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinRepsProjectiveFinrankLeNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fin_reps_projective_finrank_le_numberField : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ), ∃ (n : ℕ) (R : Fin n → ModuleCat.{0} (𝓞 E)),
    (∀ k, Module.Finite (𝓞 E) (R k) ∧ Module.Projective (𝓞 E) (R k) ∧ Module.finrank (𝓞 E) (R k) ≤ q) ∧
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∃ k, Nonempty (X ≃ₗ[𝓞 E] R k) := by
  first | exact @GlobalTheory.exists_fin_reps_projective_finrank_le | exact GlobalTheory.exists_fin_reps_projective_finrank_le | (intros; apply GlobalTheory.exists_fin_reps_projective_finrank_le <;> assumption)
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_smul_eq_sum_of_sum_toReal_eq {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m' → ℝ) (hδ : IsCell bar φ δ) (hγ : IsCell bar φ γ) (hc : ∀ j, 0 ≤ c j)
    (hs : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j)) :
    ∀ i, ∃ (k : ℕ) (a : Fin m' → ℕ), 0 < k ∧ k • δ i = ∑ j, a j • γ j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict

  have hrel : ∑ i, (ℓ (δ i) : ℝ) = ∑ j, c j * (ℓ (γ j) : ℝ) := by
    have e := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim δ γ) (c := Sum.elim (fun _ => (1 : ℝ)) (fun j => -c j)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, one_smul, neg_smul, Finset.sum_neg_distrib, hs,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at e
    simp only [Sum.elim_inl, Sum.elim_inr, one_mul, neg_mul, Finset.sum_neg_distrib] at e
    linarith

  have hlinγ := (linearOn_iff φ γ).1 hγ.linear c hc
  have hlinδ := (linearOn_iff φ δ).1 hδ.linear (fun _ => 1) (fun _ => zero_le_one)
  simp only [one_smul, one_mul] at hlinδ
  rw [hs, hlinγ] at hlinδ

  have hsum : ∑ i, ((ℓ (δ i) : ℝ) - N * φ.evalZ (δ i)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hlinδ, hrel, Finset.mul_sum]
    simp only [h1]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun j _ => by ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ (ℓ (δ i) : ℝ) - N * φ.evalZ (δ i) := fun i _ =>
    sub_nonneg.2 (h2 _ (hδ.mem i) (hδ.nonneg i))
  intro i
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ _)
  exact h3 _ (hδ.mem i) (hδ.nonneg i) (by linarith)

end GlobalTheory.PolFan
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_generators_smul_mem_other_cellCone : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m' → ℝ), IsCell bar φ δ → IsCell bar φ γ → (∀ j, 0 ≤ c j) →
    ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j) →
    ∀ i, ∃ (k : ℕ) (a : Fin m' → ℕ), 0 < k ∧ k • δ i = ∑ j, a j • γ j := by
  atlas_forward_decl GlobalTheory.PolFan.exists_smul_eq_sum_of_sum_toReal_eq
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem cell_gen_mem_cone_of_smul : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (i : Fin m) (k : ℕ) (a : Fin m' → ℕ), IsCell bar φ δ → IsCell bar φ γ → 0 < k → k • δ i = ∑ j, a j • γ j →
    ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l := by
  intro O _ bar φ X _ _ _ m m' δ γ i k a hδ hγ hk he j hj
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hδ.strict

  have eδ : φ.evalZ (k • δ i) = k * φ.evalZ (δ i) := by
    have := hδ.linear (Pi.single i (k : ℝ)) fun l => by
      by_cases h : l = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [InvFun.evalZ]
    convert this using 2
    funext x y
    simp
  have eγ : φ.evalZ (∑ j, a j • γ j) = ∑ j, (a j : ℝ) * φ.evalZ (γ j) := by
    have := hγ.linear (fun j => (a j : ℝ)) fun j => by positivity
    rw [InvFun.evalZ]
    convert this using 2
    funext x y
    simp [LinearMap.sum_apply]
  have ℓδ : (ℓ (k • δ i) : ℝ) = k * (N * φ.evalZ (δ i)) := by
    rw [map_nsmul, ← h1 i, nsmul_eq_mul]; push_cast; rfl
  have ℓγ : (ℓ (∑ j, a j • γ j) : ℝ) = ∑ j, (a j : ℝ) * ℓ (γ j) := by
    rw [map_sum]; push_cast; simp [map_nsmul]
  have key : ∑ j, (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) = 0 := by
    have e1 : (ℓ (∑ j, a j • γ j) : ℝ) = N * φ.evalZ (∑ j, a j • γ j) := by
      rw [← he, ℓδ, eδ]; ring
    rw [ℓγ, eγ, Finset.mul_sum] at e1
    simp only [mul_sub, Finset.sum_sub_distrib, e1]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => by ring
  have nn : ∀ j ∈ Finset.univ, 0 ≤ (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) := fun j _ =>
    mul_nonneg (by positivity) (sub_nonneg.2 (h2 _ (hγ.mem j) (hγ.nonneg j)))
  have z := (Finset.sum_eq_zero_iff_of_nonneg nn).1 key j (Finset.mem_univ _)
  have ha : (a j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have heq : (N : ℝ) * φ.evalZ (γ j) = ℓ (γ j) := by
    have := (mul_eq_zero.1 z).resolve_left ha
    linarith
  exact h3 _ (hγ.mem j) (hγ.nonneg j) heq

end GlobalTheory.PolFan
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_generator_mem_cone_of_smul_combination : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (i : Fin m) (k : ℕ) (a : Fin m' → ℕ), IsCell bar φ δ → IsCell bar φ γ → 0 < k → k • δ i = ∑ j, a j • γ j →
    ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l := by
  atlas_forward_decl GlobalTheory.PolFan.cell_gen_mem_cone_of_smul
end

section
section
open Finset

namespace GlobalTheory

theorem exists_pos_smul_eq_of_linearIndependent_cone {L : Type} [AddCommGroup L] {m m' : ℕ}
    (δ : Fin m → L) (γ : Fin m' → L) (i : Fin m) (k : ℕ)
    (a : Fin m' → ℕ) (hδ : LinearIndependent ℤ δ) (hk : 0 < k) (hsum : k • δ i = ∑ j, a j • γ j)
    (hγ : ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l) :
    ∃ (j : Fin m') (p r : ℕ), 0 < p ∧ 0 < r ∧ p • δ i = r • γ j := by
  classical
  have hγ' : ∀ j, ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ (0 < a j → k' • γ j = ∑ l, b l • δ l) := by
    intro j
    by_cases hj : 0 < a j
    · obtain ⟨k', b, hk', h⟩ := hγ j hj
      exact ⟨k', b, hk', fun _ => h⟩
    · exact ⟨1, 0, one_pos, fun h => absurd h hj⟩
  choose kk b hkk hb using hγ'
  let c : Fin m' → ℕ := fun j => ∏ j' ∈ univ.erase j, kk j'
  let K : ℕ := ∏ j, kk j
  have hcK : ∀ j, c j * kk j = K := fun j => by
    rw [mul_comm]; exact Finset.mul_prod_erase _ _ (mem_univ j)
  have hcpos : ∀ j, 0 < c j := fun j => Finset.prod_pos (fun j' _ => hkk j')
  have hKpos : 0 < K := Finset.prod_pos (fun j _ => hkk j)
  have hterm : ∀ j, (K * a j) • γ j = (a j * c j) • ∑ l, b j l • δ l := by
    intro j
    by_cases hj : 0 < a j
    · rw [← hb j hj, smul_smul, ← hcK j]; congr 1; ring
    · have : a j = 0 := Nat.eq_zero_of_not_pos hj
      simp [this]
  have key : (K * k) • δ i = ∑ l, (∑ j, a j * c j * b j l) • δ l := by
    calc (K * k) • δ i = K • (k • δ i) := mul_smul _ _ _
      _ = ∑ j, (K * a j) • γ j := by rw [hsum, Finset.smul_sum]; simp_rw [smul_smul]
      _ = ∑ j, (a j * c j) • ∑ l, b j l • δ l := Finset.sum_congr rfl (fun j _ => hterm j)
      _ = ∑ l, (∑ j, a j * c j * b j l) • δ l := by
          simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
  let N : Fin m → ℕ := fun l => ∑ j, a j * c j * b j l
  let g : Fin m → ℤ := fun l => (N l : ℤ) - (if l = i then ((K * k : ℕ) : ℤ) else 0)
  have hg : ∑ l, g l • δ l = 0 := by
    simp only [g, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      mem_univ, if_true, natCast_zsmul]
    rw [key]; exact sub_self _
  have hg0 := Fintype.linearIndependent_iff.mp hδ g hg
  have hN : ∀ l, N l = if l = i then K * k else 0 := by
    intro l
    have := hg0 l
    simp only [g] at this
    split_ifs at this ⊢ <;> omega
  have hNi : N i ≠ 0 := by rw [hN i, if_pos rfl]; exact (Nat.mul_pos hKpos hk).ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hNi
  have haj : 0 < a j := Nat.pos_of_ne_zero (fun h => hj (by simp [h]))
  have hbji : 0 < b j i := Nat.pos_of_ne_zero (fun h => hj (by simp [h]))
  have hbjl : ∀ l, l ≠ i → b j l = 0 := by
    intro l hl
    have h0 : N l = 0 := by rw [hN l, if_neg hl]
    have := (Finset.sum_eq_zero_iff.mp h0) j (mem_univ j)
    rcases Nat.mul_eq_zero.mp this with h | h
    · rcases Nat.mul_eq_zero.mp h with h | h
      · omega
      · exact absurd h (hcpos j).ne'
    · exact h
  have hγj : kk j • γ j = b j i • δ i := by
    rw [hb j haj, Finset.sum_eq_single i]
    · intro l _ hl; rw [hbjl l hl, zero_smul]
    · intro h; exact absurd (mem_univ i) h
  exact ⟨j, b j i, kk j, hbji, hkk j, hγj.symm⟩

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_smul_eq_of_linearIndependent_cone' : ∀ {L : Type} [AddCommGroup L] {m m' : ℕ} (δ : Fin m → L) (γ : Fin m' → L) (i : Fin m) (k : ℕ)
    (a : Fin m' → ℕ), LinearIndependent ℤ δ → 0 < k → k • δ i = ∑ j, a j • γ j →
    (∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l) →
    ∃ (j : Fin m') (p r : ℕ), 0 < p ∧ 0 < r ∧ p • δ i = r • γ j := by
  atlas_forward_decl GlobalTheory.exists_pos_smul_eq_of_linearIndependent_cone
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem balForms_zsmul_cancel {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]
    {g : ℤ} (hg : g ≠ 0) {a b : balForms bar X} (h : g • a = g • b) : a = b := by
  apply Subtype.ext
  refine LinearMap.ext₂ fun y z => ?_
  have h2 := LinearMap.congr_fun₂ (congrArg Subtype.val h) y z
  simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  exact mul_left_cancel₀ hg h2

theorem isPrim_ray_eq : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    (β β' : balForms bar X) (p r : ℕ), IsPrim bar β → IsPrim bar β' → 0 < p → 0 < r → p • β = r • β' → β = β' := by
  intro O _ bar X _ _ β β' p r hβ hβ' hp hr h
  set g := Nat.gcd p r with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hp
  obtain ⟨p₁, hp₁⟩ : g ∣ p := Nat.gcd_dvd_left p r
  obtain ⟨r₁, hr₁⟩ : g ∣ r := Nat.gcd_dvd_right p r
  have hcop : Nat.Coprime p₁ r₁ := by
    have := Nat.coprime_div_gcd_div_gcd (m := p) (n := r) hg
    rw [← hgdef] at this
    have e1 : p / g = p₁ := by rw [hp₁, Nat.mul_div_cancel_left _ hg]
    have e2 : r / g = r₁ := by rw [hr₁, Nat.mul_div_cancel_left _ hg]
    rwa [e1, e2] at this

  have h1 : (p₁ : ℤ) • β = (r₁ : ℤ) • β' := by
    apply balForms_zsmul_cancel (g := (g : ℤ)) (by exact_mod_cast hg.ne')
    rw [smul_smul, smul_smul, ← Nat.cast_mul, ← Nat.cast_mul, ← hp₁, ← hr₁, natCast_zsmul, natCast_zsmul]
    exact h

  have hbez : (p₁ : ℤ) * Nat.gcdA p₁ r₁ + (r₁ : ℤ) * Nat.gcdB p₁ r₁ = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]; rfl
  set u := Nat.gcdA p₁ r₁
  set v := Nat.gcdB p₁ r₁
  have hr1 : r₁ = 1 := by
    apply hβ r₁ (u • β' + v • β)
    calc β = ((p₁ : ℤ) * u + (r₁ : ℤ) * v) • β := by rw [hbez, one_smul]
      _ = u • ((p₁ : ℤ) • β) + (r₁ : ℤ) • (v • β) := by
          rw [add_smul, smul_smul, smul_smul, mul_comm (p₁ : ℤ) u]
      _ = r₁ • (u • β' + v • β) := by
          rw [h1, smul_smul, mul_comm u, ← smul_smul, ← smul_add, natCast_zsmul]
  have hp1 : p₁ = 1 := by
    apply hβ' p₁ (u • β' + v • β)
    calc β' = ((p₁ : ℤ) * u + (r₁ : ℤ) * v) • β' := by rw [hbez, one_smul]
      _ = (p₁ : ℤ) • (u • β') + v • ((r₁ : ℤ) • β') := by
          rw [add_smul, smul_smul, smul_smul, mul_comm (r₁ : ℤ) v]
      _ = p₁ • (u • β' + v • β) := by
          rw [← h1, smul_smul v, mul_comm v, ← smul_smul, ← smul_add, natCast_zsmul]
  rw [hr1, hp1] at h1
  simpa using h1

end GlobalTheory.PolFan
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveBalancedForm_eq_of_same_ray : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    (β β' : balForms bar X) (p r : ℕ), IsPrim bar β → IsPrim bar β' → 0 < p → 0 < r → p • β = r • β' → β = β' := by
  atlas_forward_decl GlobalTheory.PolFan.isPrim_ray_eq
end

section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.CellClass

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [AddCommGroup X₁] [Module O X₁]

theorem isCell_pull_equiv [Module.Finite O X] [Module.Finite O X₁] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar φ γ) (e : X ≃ₗ[O] X₁) : IsCell bar φ fun i => pull e.toLinearMap (γ i) :=
  ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
    IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩

def pullLin (r : X →ₗ[O] X₁) : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pull r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_injective {r : X →ₗ[O] X₁} (hr : Function.Surjective r) : Function.Injective (pull r : LinearMap.BilinForm ℤ X₁ → LinearMap.BilinForm ℤ X) := by
  intro β β' h
  refine LinearMap.ext₂ fun a b => ?_
  obtain ⟨a, rfl⟩ := hr a
  obtain ⟨b, rfl⟩ := hr b
  exact LinearMap.congr_fun₂ h a b

theorem linearIndependent_pull_equiv {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X₁} (h : LinearIndependent ℤ γ)
    (e : X ≃ₗ[O] X₁) : LinearIndependent ℤ fun i => pull e.toLinearMap (γ i) :=
  h.map' (pullLin e.toLinearMap) (LinearMap.ker_eq_bot.2 (pull_injective e.surjective))

theorem isPrim_pull_equiv (e : X ≃ₗ[O] X₁) {β : LinearMap.BilinForm ℤ X₁} (hβ : β ∈ balForms bar X₁)
    (h : IsPrim bar (⟨β, hβ⟩ : balForms bar X₁)) :
    IsPrim bar (⟨pull e.toLinearMap β, pull_mem _ hβ⟩ : balForms bar X) := by
  intro k β' hk
  refine h k ⟨pull e.symm.toLinearMap β'.1, pull_mem _ β'.2⟩ (Subtype.ext (LinearMap.ext₂ fun a b => ?_))
  have := LinearMap.congr_fun₂ (congrArg Subtype.val hk) (e.symm a) (e.symm b)
  simpa using this

end Transport

theorem perModule {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E))
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (hX : IsPolyFanOn H.bar φ X) :
    ∃ T : Set (LinearMap.BilinForm ℤ X), T.Finite ∧ ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X)
      (h : IsCell H.bar φ δ), LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
      ∃ e : X ≃ₗ[𝓞 E] X, ∀ i, pull e.toLinearMap (δ i) ∈ T := by
  classical
  obtain ⟨S, hS, hcov⟩ := hX.finite
  let U : LinearMap.BilinForm ℤ X → Set (LinearMap.BilinForm ℤ X) := fun s =>
    {t | ∃ ht : t ∈ balForms H.bar X, IsPrim H.bar (⟨t, ht⟩ : balForms H.bar X) ∧
      ∃ p r : ℕ, 0 < p ∧ 0 < r ∧ p • t = r • s}
  have hU : ∀ s, (U s).Subsingleton := by
    rintro s t ⟨ht, hpt, p, r, hp, hr, he⟩ t' ⟨ht', hpt', p', r', hp', hr', he'⟩
    have key : (r' * p) • t = (r * p') • t' := by
      rw [mul_smul, he, mul_smul, he', smul_comm]
    have := GlobalTheory.T.primitiveBalancedForm_eq_of_same_ray H.bar ⟨t, ht⟩ ⟨t', ht'⟩ (r' * p) (r * p') hpt hpt' (by positivity) (by positivity)
      (Subtype.ext (by simpa using key))
    exact congrArg Subtype.val this
  refine ⟨⋃ s ∈ S, U s, hS.biUnion fun s _ => (hU s).finite, fun m δ h hli hprim => ?_⟩
  have hB : ∑ i, (1 : ℝ) • toReal (δ i) ∈ psdCone H.bar X :=
    ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X m δ (fun _ => 1) h.mem h.nonneg (fun _ => zero_le_one)
  obtain ⟨e, m', γ, c, hγ, hγS, hc, hsum⟩ := hcov _ hB
  set γ' : Fin m' → LinearMap.BilinForm ℤ X := fun j => pull e.symm.toLinearMap (γ j) with hγ'def
  have hγ' : IsCell H.bar φ γ' := isCell_pull_equiv hγ e.symm
  have hsum' : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ' j) := by
    refine LinearMap.ext₂ fun y z => ?_
    have := LinearMap.congr_fun₂ hsum (e.symm y) (e.symm z)
    simpa [LinearMap.sum_apply, γ'] using this
  refine ⟨e, fun i => ?_⟩
  obtain ⟨k, a, hk, hka⟩ := GlobalTheory.T.cell_generators_smul_mem_other_cellCone H.bar φ δ γ' c h hγ' hc hsum' i
  obtain ⟨j, p, r, hp, hr, hpr⟩ :=
    GlobalTheory.T.exists_pos_smul_eq_of_linearIndependent_cone' δ γ' i k a hli hk hka (GlobalTheory.T.cell_generator_mem_cone_of_smul_combination H.bar φ δ γ' i k a h hγ' hk hka)
  refine Set.mem_biUnion (hγS j) ⟨pull_mem _ (h.mem i), isPrim_pull_equiv e (h.mem i) (hprim i), p, r, hp, hr, ?_⟩
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ hpr (e y) (e z)
  simpa [γ'] using this

theorem multCellsAmong_of_isPolyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ : InvFun (𝓞 E)), IsPolyFan H.bar q φ → ∀ M : ℕ, ∃ n : ℕ, MultCellsAmong H.bar q φ M n := by
  intro E _ _ _ H q φ hφ M
  classical
  obtain ⟨n, R, hR, hcls⟩ := GlobalTheory.T.exists_fin_reps_projective_finrank_le_numberField E q
  have key : ∀ k, letI := (hR k).1; ∃ T : Set (LinearMap.BilinForm ℤ (R k)), T.Finite ∧
      ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ (R k)) (h : IsCell H.bar φ δ), LinearIndependent ℤ δ →
        (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar (R k))) →
        ∃ e : (R k) ≃ₗ[𝓞 E] (R k), ∀ i, pull e.toLinearMap (δ i) ∈ T := fun k => by
    letI := (hR k).1
    haveI := (hR k).2.1
    exact perModule H φ (R k) (hφ (R k) (hR k).2.2)
  choose T hTfin hT using key
  haveI : ∀ k, Finite (T k) := fun k => (hTfin k).to_subtype
  let D := Σ k : Fin n, Σ m : Fin (Nat.card (T k) + 1), (Fin m → T k)
  let g : D → FormFamily (𝓞 E) := fun d => ⟨R d.1, d.2.1, fun i => (d.2.2 i : LinearMap.BilinForm ℤ (R d.1))⟩
  obtain ⟨N, ⟨eq⟩⟩ := Finite.exists_equiv_fin D
  refine ⟨N, fun k' => g (eq.symm k'), fun X _ _ _ _ hX m δ hδ => ?_⟩
  obtain ⟨hcell, hli, hprim, -⟩ := hδ
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  letI := (hR k).1
  let δ' : Fin m → LinearMap.BilinForm ℤ (R k) := fun i => pull f.symm.toLinearMap (δ i)
  have hcell' : IsCell H.bar φ δ' := isCell_pull_equiv hcell f.symm
  have hli' : LinearIndependent ℤ δ' := linearIndependent_pull_equiv hli f.symm
  have hprim' : ∀ i, IsPrim H.bar (⟨δ' i, hcell'.mem i⟩ : balForms H.bar (R k)) := fun i =>
    isPrim_pull_equiv f.symm (hcell.mem i) (hprim i)
  obtain ⟨e, he⟩ := hT k m δ' hcell' hli' hprim'
  let t : Fin m → T k := fun i => ⟨_, he i⟩
  have ht : Function.Injective t := fun i j hij =>
    hli'.injective (pull_injective e.surjective (congrArg Subtype.val hij))
  have hm : m < Nat.card (T k) + 1 := by
    have := Nat.card_le_card_of_injective t ht
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  refine ⟨eq ⟨k, ⟨m, hm⟩, t⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  refine ⟨f.trans e.symm, Equiv.refl (Fin m), fun i => LinearMap.ext₂ fun y z => ?_⟩
  simp [g, t, δ']

end GlobalTheory.PolFan.CellClass
end
end
