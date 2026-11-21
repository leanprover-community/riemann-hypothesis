import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorZeroOneBarycentresPolyFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyFanFaceCutByIntLinearFormIsCellStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntLinearFormCuttingSubcell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimLeOfAddCellGenerators

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedFormIndicator_zeroOne_barycentres_polyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → lab.evalZ β = ((i + 1 : ℕ) : ℝ)) ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms H.bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone v β → InRCone v β' → β = β') ∧ (∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone v β₀) := by
  first | exact @GlobalTheory.PolFan.Mark.exists_markFun_props | exact GlobalTheory.PolFan.Mark.exists_markFun_props | (intros; apply GlobalTheory.PolFan.Mark.exists_markFun_props <;> assumption)
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intLinearForm_cutting_subcell : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m n : ℕ) (G : Fin m → LinearMap.BilinForm ℤ X) (δ : Fin n → LinearMap.BilinForm ℤ X), IsCell bar φ G → IsCell bar φ δ → (∀ k, InRCone G (δ k)) → ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ h (G j)) ∧ (∀ k, h (δ k) = 0) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone G β → h β = 0 → InRCone δ β := by
  first | exact @GlobalTheory.PolFan.exists_cut_of_cell_le | exact GlobalTheory.PolFan.exists_cut_of_cell_le | (intros; apply GlobalTheory.PolFan.exists_cut_of_cell_le <;> assumption)
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrierDim_le_of_add_cell_generators : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ (b : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β := by
  first | exact @GlobalTheory.PolFan.carrierDim_le_of_add_cell | exact GlobalTheory.PolFan.carrierDim_le_of_add_cell | (intros; apply GlobalTheory.PolFan.carrierDim_le_of_add_cell <;> assumption)
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

section Enumerate

theorem exists_enum_fin {n : ℕ} (P : Fin n → Prop) :
    ∃ (p : ℕ) (e : Fin p ↪ Fin n), ∀ k, P k ↔ k ∈ Set.range e := by
  classical
  refine ⟨(Finset.univ.filter P).card, ((Finset.univ.filter P).orderEmbOfFin rfl).toEmbedding, fun k => ?_⟩
  have := (Finset.univ.filter P).range_orderEmbOfFin rfl
  change _ ↔ k ∈ Set.range ((Finset.univ.filter P).orderEmbOfFin rfl)
  rw [this]
  simp

theorem exists_append_emb {p r b a : ℕ} (eS : Fin p ↪ Fin b) (eT : Fin r ↪ Fin a) :
    ∃ s : Fin (p + r) ↪ Fin (b + a), (∀ k, s (Fin.castAdd r k) = Fin.castAdd a (eS k)) ∧
      ∀ j, s (Fin.natAdd p j) = Fin.natAdd b (eT j) := by
  refine ⟨(finSumFinEquiv.symm.toEmbedding.trans (Function.Embedding.sumMap eS eT)).trans finSumFinEquiv.toEmbedding,
    fun k => ?_, fun j => ?_⟩
  · simp
  · simp

theorem exists_extend_coeff {R : Type*} [Semiring R] {p n : ℕ} (e : Fin p ↪ Fin n) (d : Fin p → R) :
    ∃ r : Fin n → R, (∀ j, r (e j) = d j) ∧ (∀ x, x ∉ Set.range e → r x = 0) ∧
      ∀ {M : Type _} [AddCommMonoid M] [Module R M] (f : Fin n → M), ∑ x, r x • f x = ∑ j, d j • f (e j) := by
  classical
  have h1 : ∀ j, Function.extend e d 0 (e j) = d j := fun j => e.injective.extend_apply _ _ _
  have h2 : ∀ x, x ∉ Set.range e → Function.extend e d 0 x = 0 := fun x hx => by
    rw [Function.extend_apply' _ _ _ (by simpa using hx)]
    rfl
  refine ⟨Function.extend e d 0, h1, h2, fun f => ?_⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) (fun x _ hx => ?_), Finset.sum_map]
  · simp only [Function.Embedding.coeFn_mk, h1]
  · rw [h2 x (fun ⟨j, hj⟩ => hx (by simp [← hj])), zero_smul]

theorem exists_perm_append_cons {α : Type*} {p q : ℕ} (x : α) (f : Fin p → α) (g : Fin q → α) :
    ∃ e : Fin (p + (q + 1)) ≃ Fin (p + q + 1), ∀ i,
      Fin.append f (Fin.cons x g : Fin (q + 1) → α) i = (Fin.cons x (Fin.append f g) : Fin (p + q + 1) → α) (e i) := by
  let F : Fin (p + (q + 1)) → Fin (p + q + 1) := fun i =>
    if h : (i : ℕ) < p then ⟨i + 1, by omega⟩ else if (i : ℕ) = p then ⟨0, by omega⟩ else ⟨i, by have := i.isLt; omega⟩
  let G : Fin (p + q + 1) → Fin (p + (q + 1)) := fun j =>
    if (j : ℕ) = 0 then ⟨p, by omega⟩ else if (j : ℕ) ≤ p then ⟨j - 1, by omega⟩ else ⟨j, by have := j.isLt; omega⟩
  have hF : ∀ i, (F i : ℕ) = if (i : ℕ) < p then (i : ℕ) + 1 else if (i : ℕ) = p then 0 else (i : ℕ) := fun i => by
    simp only [F]; split_ifs <;> rfl
  have hG : ∀ j, (G j : ℕ) = if (j : ℕ) = 0 then p else if (j : ℕ) ≤ p then (j : ℕ) - 1 else (j : ℕ) := fun j => by
    simp only [G]; split_ifs <;> rfl
  have hGF : ∀ i, G (F i) = i := fun i => by
    apply Fin.ext
    rw [hG, hF]
    split_ifs <;> first | contradiction | omega
  have hFG : ∀ j, F (G j) = j := fun j => by
    apply Fin.ext
    rw [hF, hG]
    split_ifs <;> first | contradiction | omega
  refine ⟨⟨F, G, hGF, hFG⟩, fun i => ?_⟩
  change _ = (Fin.cons x (Fin.append f g) : Fin (p + q + 1) → α) (F i)
  induction i using Fin.addCases with
  | left k =>
    have : F (Fin.castAdd (q + 1) k) = (Fin.castAdd q k).succ := Fin.ext (by simp [F])
    rw [this, Fin.cons_succ, Fin.append_left, Fin.append_left]
  | right l =>
    rw [Fin.append_right]
    induction l using Fin.cases with
    | zero =>
      have : F (Fin.natAdd p 0) = 0 := Fin.ext (by simp [F])
      rw [this, Fin.cons_zero, Fin.cons_zero]
    | succ j =>
      have : F (Fin.natAdd p j.succ) = (Fin.natAdd p j).succ := Fin.ext (by simp [F]; omega)
      rw [this, Fin.cons_succ, Fin.cons_succ, Fin.append_right]

end Enumerate

section Step

theorem star_cell_bary_step : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab φ' w : InvFun O) (i : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X), IsCell bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) → (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β → ((i + 1 : ℕ) : ℝ) < lab.evalZ β) → (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n) → (∀ (m' : ℕ) (s : Fin m' ↪ Fin b) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell bar ψ (fun j => v (s j))) → (∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₁ ∈ balForms bar X, (∀ y, 0 ≤ β₁ y y) ∧ w.evalZ β₁ = 1 ∧ InRCone γ β₁) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone (Fin.append v u) β → InRCone (Fin.append v u) β' → β = β') → (∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β) → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → lab.evalZ β₀ = ((i + 1 : ℕ) : ℝ) → InRCone (Fin.append v u) β₀ → (∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut (Fin.append v u) s h → 0 < h β₀ → IsCell bar φ' (Fin.cons β₀ fun j => Fin.append v u (s j))) → ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut (Fin.append v u) s h → 0 < h β₀ → ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X), IsCell bar φ' (Fin.append v' u') ∧ IsCell bar ψ v' ∧ (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) k)) ∧ Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β → (i : ℝ) < lab.evalZ β) ∧ ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
  classical
  intro O _ bar ψ lab φ' w i X _ _ _ b a v u hv hinj hlab hle hgt hind hnat hface hex huniq hmono β₀ hβ₀ hβ₀n hw hl0 hcone
    hstar m' s h hcut hpos
  set G := Fin.append v u with hGdef
  have hGv : ∀ k, G (Fin.castAdd a k) = v k := fun k => Fin.append_left v u k
  have hGu : ∀ j, G (Fin.natAdd b j) = u j := fun j => Fin.append_right v u j
  have hvG : ∀ k, InRCone G (v k) := fun k => hGv k ▸ inRCone_self G _
  have huG : ∀ j, InRCone G (u j) := fun j => hGu j ▸ inRCone_self G _

  have hv0 : InRCone v β₀ := by
    by_contra hn
    have := hgt β₀ hβ₀ hβ₀n hcone hn
    rw [hl0] at this
    exact lt_irrefl _ this

  obtain ⟨p, eS, heS⟩ := exists_enum_fin (fun k => h (v k) = 0)
  obtain ⟨r, eT, heT⟩ := exists_enum_fin (fun j => h (u j) = 0)
  obtain ⟨s', hs1, hs2⟩ := exists_append_emb eS eT
  set v' : Fin p → LinearMap.BilinForm ℤ X := fun k => v (eS k) with hv'def
  set uT : Fin r → LinearMap.BilinForm ℤ X := fun j => u (eT j) with huTdef
  set u' : Fin (r + 1) → LinearMap.BilinForm ℤ X := Fin.cons β₀ uT with hu'def
  have hvS0 : ∀ k, h (v' k) = 0 := fun k => (heS _).2 ⟨k, rfl⟩
  have huT0 : ∀ j, h (uT j) = 0 := fun j => (heT _).2 ⟨j, rfl⟩
  have hcomp : (fun j => G (s' j)) = Fin.append v' uT := funext fun j => by
    induction j using Fin.addCases with
    | left k => simp only [hs1, hGv, Fin.append_left, hv'def]
    | right l => simp only [hs2, hGu, Fin.append_right, huTdef]
  have hz : ∀ x, h (Fin.append v' uT x) = 0 := fun x => by
    induction x using Fin.addCases with
    | left k => rw [Fin.append_left]; exact hvS0 k
    | right l => rw [Fin.append_right]; exact huT0 l
  have hcut' : IsFaceCut G s' h := by
    refine ⟨hcut.1, fun j => ⟨fun h0 => ?_, ?_⟩⟩
    · induction j using Fin.addCases with
      | left k =>
        rw [hGv] at h0
        obtain ⟨k', rfl⟩ := (heS k).1 h0
        exact ⟨_, hs1 k'⟩
      | right l =>
        rw [hGu] at h0
        obtain ⟨l', rfl⟩ := (heT l).1 h0
        exact ⟨_, hs2 l'⟩
    · rintro ⟨x, rfl⟩
      rw [show G (s' x) = Fin.append v' uT x from congrFun hcomp x]
      exact hz x

  have hc1 := hstar (p + r) s' h hcut' hpos
  rw [hcomp] at hc1
  obtain ⟨e, he⟩ := exists_perm_append_cons β₀ v' uT
  have hcell : IsCell bar φ' (Fin.append v' u') := by
    have := hc1.reindex e
    convert this using 1
    funext x
    exact he x

  have hcellv : IsCell bar ψ v' := hface p eS h ⟨fun k => by
    have := hcut.1 (Fin.castAdd a k); rwa [hGv] at this, fun k => (heS k)⟩

  have hm0 : InRCone (Fin.append v' u') β₀ := by
    have := inRCone_self (Fin.append v' u') (Fin.natAdd p 0)
    rwa [Fin.append_right, hu'def, Fin.cons_zero] at this
  have hmv : ∀ k, InRCone (Fin.append v' u') (v' k) := fun k => by
    have := inRCone_self (Fin.append v' u') (Fin.castAdd (r + 1) k)
    rwa [Fin.append_left] at this
  have hmu : ∀ j, InRCone (Fin.append v' u') (uT j) := fun j => by
    have := inRCone_self (Fin.append v' u') (Fin.natAdd p j.succ)
    rwa [Fin.append_right, hu'def, Fin.cons_succ] at this

  have hG' : ∀ x, InRCone G (Fin.append v' u' x) := fun x => by
    induction x using Fin.addCases with
    | left k => rw [Fin.append_left]; exact hvG _
    | right l =>
      rw [Fin.append_right]
      induction l using Fin.cases with
      | zero => rw [hu'def, Fin.cons_zero]; exact hcone
      | succ j => rw [hu'def, Fin.cons_succ]; exact huG _
  have hv'v : ∀ k, InRCone v (v' k) := fun k => inRCone_self v _
  refine ⟨p, r + 1, v', u', hcell, hcellv, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro k
    induction k using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hm0
    | succ j =>
      rw [Fin.cons_succ]
      have h0 : h (G (s j)) = 0 := (hcut.2 _).2 ⟨j, rfl⟩
      generalize s j = x at h0 ⊢
      induction x using Fin.addCases with
      | left k =>
        rw [hGv] at h0 ⊢
        obtain ⟨k', rfl⟩ := (heS k).1 h0
        exact hmv k'
      | right l =>
        rw [hGu] at h0 ⊢
        obtain ⟨l', rfl⟩ := (heT l).1 h0
        exact hmu l'

  · have hl0' : lab.evalZ (u' 0) = ((i + 1 : ℕ) : ℝ) := by rw [hu'def, Fin.cons_zero]; exact hl0
    have hls : ∀ j, lab.evalZ (u' j.succ) = lab.evalZ (u (eT j)) := fun j => by rw [hu'def, Fin.cons_succ]
    intro x y hxy
    simp only at hxy
    induction x using Fin.cases with
    | zero =>
      induction y using Fin.cases with
      | zero => rfl
      | succ j' =>
        rw [hl0', hls] at hxy
        exact absurd hxy (ne_of_lt (hlab _))
    | succ j =>
      induction y using Fin.cases with
      | zero =>
        rw [hl0', hls] at hxy
        exact absurd hxy.symm (ne_of_lt (hlab _))
      | succ j' =>
        rw [hls, hls] at hxy
        rw [eT.injective (hinj hxy)]

  · intro j
    induction j using Fin.cases with
    | zero => rw [hu'def, Fin.cons_zero, hl0]; push_cast; linarith
    | succ j =>
      rw [hu'def, Fin.cons_succ]
      have := hlab (eT j)
      push_cast at this
      linarith

  · intro β hβ hβn hin
    have hinv : InRCone v β := inRCone_trans hv'v hin
    have h1 := hle β hβ hβn hinv
    obtain ⟨n, hn⟩ := hnat β hβ hβn
    rw [hn] at h1 ⊢
    have h2 : n ≤ i + 1 := by exact_mod_cast h1
    rcases Nat.lt_or_ge n (i + 1) with h3 | h3
    · exact_mod_cast Nat.lt_succ_iff.1 h3
    · exfalso
      have h4 : n = i + 1 := le_antisymm h2 h3
      obtain ⟨β₁, hβ₁, hβ₁n, hw₁, hc₁⟩ := hex p v' hcellv β hβ hβn hin (by rw [hn, h4])
      have hβ₁G : InRCone G β₁ := inRCone_trans (fun k => inRCone_trans (fun k' => hvG k') (hv'v k)) hc₁
      have := huniq β₁ hβ₁ hβ₁n β₀ hβ₀ hβ₀n hw₁ hw hβ₁G hcone
      subst this
      obtain ⟨c, hc, ec⟩ := hc₁
      have h5 := apply_eq_of_toReal_eq ec h
      simp only [hvS0, Int.cast_zero, mul_zero, Finset.sum_const_zero] at h5
      have : (0 : ℝ) < h β₁ := by exact_mod_cast hpos
      linarith

  · intro β hβ hβn hin hnot
    have hinG : InRCone G β := inRCone_trans hG' hin
    by_cases hbv : InRCone v β
    · obtain ⟨c, hc, ec⟩ := hin
      rw [Fin.sum_univ_add] at ec
      simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_succ, hu'def, Fin.cons_zero, Fin.cons_succ] at ec
      set c₀ := c (Fin.natAdd p 0)
      set cv : Fin p → ℝ := fun k => c (Fin.castAdd (r + 1) k) with hcv
      set d : Fin r → ℝ := fun j => c (Fin.natAdd p j.succ) with hd
      obtain ⟨ee, -, e1⟩ := id hbv
      obtain ⟨f, -, e2⟩ := id hv0
      obtain ⟨rd, -, -, hrd⟩ := exists_extend_coeff eT d
      obtain ⟨rc, hrc1, hrc2, hrc⟩ := exists_extend_coeff eS cv
      have hrel : ∑ j, rd j • toReal (u j) = ∑ k, (ee k - c₀ * f k - rc k) • toReal (v k) := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
        rw [hrd, hrc, ← e1, ← e2, ec]
        abel
      have hd0 : rd = 0 := eq_zero_of_toReal_rel hind hrel
      have hdz : ∑ j, d j • toReal (uT j) = 0 := by
        have := hrd (fun j => toReal (u j))
        simp only [hd0, Pi.zero_apply, zero_smul, Finset.sum_const_zero] at this
        exact this.symm
      have e' : toReal β = c₀ • toReal β₀ + ∑ k, rc k • toReal (v k) := by
        rw [hrc, ec, hdz, add_zero, add_comm]
      rcases (hc (Fin.natAdd p 0)).eq_or_lt with h0 | h0
      · exfalso
        apply hnot
        refine ⟨cv, fun k => hc _, ?_⟩
        have h0' : c₀ = 0 := h0.symm
        rw [ec, hdz, h0', zero_smul, add_zero, add_zero]
      · have hrcn : ∀ k, 0 ≤ rc k := fun k => by
          by_cases hk : k ∈ Set.range eS
          · obtain ⟨k', rfl⟩ := hk; rw [hrc1]; exact hc _
          · rw [hrc2 k hk]
        have := hmono β₀ hβ₀ hβ₀n β hβ hβn hv0 c₀ rc h0 hrcn e'
        rw [hl0] at this
        push_cast at this ⊢
        linarith
    · have := hgt β hβ hβn hinG hbv
      push_cast at this ⊢
      linarith

  · intro d c hrel
    rw [Fin.sum_univ_succ] at hrel
    simp only [hu'def, Fin.cons_zero, Fin.cons_succ] at hrel
    have h1 := congrArg h hrel
    simp only [map_add, map_sum, map_zsmul, hvS0, huT0, smul_zero, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero] at h1
    have hc0 : c 0 = 0 := (mul_eq_zero.1 h1).resolve_right hpos.ne'
    rw [hc0, zero_smul, zero_add] at hrel
    obtain ⟨rc, hrc1, -, hrc⟩ := exists_extend_coeff eT (fun j => c j.succ)
    obtain ⟨rd, -, -, hrd⟩ := exists_extend_coeff eS d
    have hz := hind rd rc (by rw [hrc, hrd]; exact hrel)
    funext x
    induction x using Fin.cases with
    | zero => exact hc0
    | succ j =>
      have := hrc1 j
      rw [hz] at this
      exact this.symm

end Step

end GlobalTheory.PolFan
end
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_barycentre_cell_next_stage : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab φ' w : InvFun O) (i : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X), IsCell bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) → (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β → ((i + 1 : ℕ) : ℝ) < lab.evalZ β) → (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n) → (∀ (m' : ℕ) (s : Fin m' ↪ Fin b) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell bar ψ (fun j => v (s j))) → (∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₁ ∈ balForms bar X, (∀ y, 0 ≤ β₁ y y) ∧ w.evalZ β₁ = 1 ∧ InRCone γ β₁) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone (Fin.append v u) β → InRCone (Fin.append v u) β' → β = β') → (∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β) → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → lab.evalZ β₀ = ((i + 1 : ℕ) : ℝ) → InRCone (Fin.append v u) β₀ → (∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut (Fin.append v u) s h → 0 < h β₀ → IsCell bar φ' (Fin.cons β₀ fun j => Fin.append v u (s j))) → ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut (Fin.append v u) s h → 0 < h β₀ → ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X), IsCell bar φ' (Fin.append v' u') ∧ IsCell bar ψ v' ∧ (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) k)) ∧ Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β → (i : ℝ) < lab.evalZ β) ∧ ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
  atlas_forward_decl GlobalTheory.PolFan.star_cell_bary_step
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

section Helpers

variable {X : Type} [AddCommGroup X]

theorem inRCone_append_left {b a : ℕ} (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X)
    {β : LinearMap.BilinForm ℤ X} (h : InRCone v β) : InRCone (Fin.append v u) β :=
  inRCone_trans (fun k => by simpa using inRCone_self (Fin.append v u) (Fin.castAdd a k)) h

theorem inRCone_cons_of {n m : ℕ} (β₀ : LinearMap.BilinForm ℤ X) {F : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (h : InRCone F β) : InRCone (Fin.cons β₀ F : Fin (m + 1) → _) β :=
  inRCone_trans (fun k => by simpa using inRCone_self (Fin.cons β₀ F : Fin (m + 1) → _) k.succ) h

theorem inRCone_cons_mono {n m : ℕ} (β₀ : LinearMap.BilinForm ℤ X) {F : Fin m → LinearMap.BilinForm ℤ X}
    {δ : Fin n → LinearMap.BilinForm ℤ X} (h : ∀ k, InRCone F (δ k)) :
    ∀ k, InRCone (Fin.cons β₀ F : Fin (m + 1) → _) ((Fin.cons β₀ δ : Fin (n + 1) → _) k) := by
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · simpa using inRCone_self (Fin.cons β₀ F : Fin (m + 1) → _) 0
  · simpa using inRCone_cons_of (n := n) β₀ (h k)

theorem inRCone_comp_of {m m' : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} (s : Fin m' ↪ Fin m) {c : Fin m → ℝ}
    (hc : ∀ j, 0 ≤ c j) {β : LinearMap.BilinForm ℤ X} (hβ : toReal β = ∑ j, c j • toReal (G j))
    (h0 : ∀ j, j ∉ Set.range s → c j = 0) : InRCone (fun l => G (s l)) β := by
  refine ⟨fun l => c (s l), fun l => hc _, ?_⟩
  rw [hβ]
  symm
  exact Fintype.sum_of_injective s s.injective _ _ (fun j hj => by rw [h0 j hj, zero_smul]) fun l => rfl

theorem coeff_eq_zero_of_apply {m : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ j, 0 ≤ c j)
    {β : LinearMap.BilinForm ℤ X} (hβ : toReal β = ∑ j, c j • toReal (G j)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hG : ∀ j, 0 ≤ h (G j)) (h0 : h β = 0) (j : Fin m) (hj : h (G j) ≠ 0) : c j = 0 := by
  have e := apply_eq_of_toReal_eq hβ h
  rw [h0, Int.cast_zero] at e
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ c j * (h (G j) : ℝ) := fun j _ => mul_nonneg (hc j) (by exact_mod_cast hG j)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 e.symm j (Finset.mem_univ _)
  exact (mul_eq_zero.1 this).resolve_right (by exact_mod_cast hj)

theorem exists_faceCut {m : ℕ} (G : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hG : ∀ j, 0 ≤ h (G j)) : ∃ (m' : ℕ) (s : Fin m' ↪ Fin m), IsFaceCut G s h := by
  classical
  let S := Finset.univ.filter fun j => h (G j) = 0
  refine ⟨S.card, (S.orderEmbOfFin rfl).toEmbedding, hG, fun j => ?_⟩
  have : Set.range (S.orderEmbOfFin rfl).toEmbedding = (S : Set (Fin m)) := by
    simp [Finset.range_orderEmbOfFin]
  rw [this]
  simp [S]

end Helpers

section Reduce

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem reduce_of_not_mem {m n : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {γ : Fin n → LinearMap.BilinForm ℤ X}
    (hG : IsCell bar φ G) (hγ : IsCell bar φ γ) (hcov : ∀ k, InRCone G (γ k)) {β₀ : LinearMap.BilinForm ℤ X}
    (hb : β₀ ∈ balForms bar X) (hp : ∀ y, 0 ≤ β₀ y y) (hin : InRCone G β₀) (hnin : ¬ InRCone γ β₀) :
    ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut G s h ∧ 0 < h β₀ ∧
      ∀ k, InRCone (fun l => G (s l)) (γ k) := by
  obtain ⟨h, hh1, hh2, hh3⟩ := GlobalTheory.T.exists_intLinearForm_cutting_subcell O bar φ X m n G γ hG hγ hcov
  obtain ⟨m', s, hs⟩ := exists_faceCut G h hh1
  refine ⟨m', s, h, hs, ?_, fun k => ?_⟩
  · rcases (hin.apply_nonneg h hh1).eq_or_lt with e | e
    · exact (hnin (hh3 β₀ hb hp hin e.symm)).elim
    · exact e
  · obtain ⟨c, hc, e⟩ := hcov k
    exact inRCone_comp_of s hc e fun j hj =>
      coeff_eq_zero_of_apply hc e h hh1 (hh2 k) j fun h0 => hj ((hs.2 j).1 h0)

theorem reduce_of_mem {m n n' : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {δ : Fin n → LinearMap.BilinForm ℤ X}
    (hG : IsCell bar φ G) (hδ : IsCell bar φ δ) (hcov : ∀ k, InRCone G (δ k)) {β₀ : LinearMap.BilinForm ℤ X}
    (hin : InRCone δ β₀) {s : Fin n' ↪ Fin n} {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hcut : IsFaceCut δ s h)
    (hpos : 0 < h β₀) :
    ∃ (m' : ℕ) (s' : Fin m' ↪ Fin m) (h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut G s' h' ∧ 0 < h' β₀ ∧
      ∀ k, InRCone (fun l => G (s' l)) (δ (s k)) := by
  obtain ⟨h₁, hh1, hh2, hh3⟩ := GlobalTheory.T.exists_intLinearForm_cutting_subcell O bar φ X m n G δ hG hδ hcov
  set K : ℤ := 1 + ∑ j, |h (G j)| with hK
  have hKj : ∀ j, |h (G j)| < K := fun j => by
    have := Finset.single_le_sum (f := fun j => |h (G j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  let h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := K • h₁ + h
  have hv : ∀ β, h' β = K * h₁ β + h β := fun β => rfl
  have hnn : ∀ j, 0 ≤ h' (G j) := fun j => by
    rw [hv]
    rcases (hh1 j).eq_or_lt with e | e
    · rw [← e, mul_zero, zero_add]
      exact (hh3 _ (hG.mem j) (hG.nonneg j) (inRCone_self G j) e.symm).apply_nonneg h hcut.1
    · have h1 : 1 ≤ h₁ (G j) := e
      have := hKj j
      have h2 : -K < h (G j) := by have := neg_abs_le (h (G j)); linarith
      have hK0 : 0 < K := lt_of_le_of_lt (abs_nonneg _) (hKj j)
      have h3 : K ≤ K * h₁ (G j) := le_mul_of_one_le_right hK0.le h1
      linarith
  obtain ⟨m', s', hs'⟩ := exists_faceCut G h' hnn
  have hz : ∀ β, InRCone δ β → h₁ β = 0 := fun β hβ => by
    obtain ⟨c, _, e⟩ := hβ
    have := apply_eq_of_toReal_eq e h₁
    simp only [hh2, Int.cast_zero, mul_zero, Finset.sum_const_zero] at this
    exact_mod_cast this
  refine ⟨m', s', h', hs', by rw [hv, hz β₀ hin, mul_zero, zero_add]; exact hpos, fun k => ?_⟩
  obtain ⟨c, hc, e⟩ := hcov (s k)
  have h0 : h' (δ (s k)) = 0 := by
    rw [hv, hz _ (inRCone_self δ _), mul_zero, zero_add]
    exact (hcut.2 _).2 ⟨k, rfl⟩
  exact inRCone_comp_of s' hc e fun j hj => coeff_eq_zero_of_apply hc e h' hnn h0 j fun h0 => hj ((hs'.2 j).1 h0)

end Reduce

theorem baryStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab φ : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → IsTwInv H φ → IsBaryStage H.bar q ψ lab φ (i + 1) → ∃ φ' : InvFun (𝓞 E), IsTwInv H φ' ∧ IsBaryStage H.bar q ψ lab φ' i := by
  intro E _ _ _ H q ψ lab φ i hdom hψ hψt hlt hcar hφt hst
  obtain ⟨w, hwt, hw⟩ := GlobalTheory.T.markedFormIndicator_zeroOne_barycentres_polyFan E H q ψ lab i hdom hψ hψt hlt hcar
  obtain ⟨hφp, hφs, hφc⟩ := hst
  have hcen : IsCentreSet H.bar q φ w := by
    intro X _ _ _ _ hX
    obtain ⟨h1, h2, h3, h4, -⟩ := hw X hX
    refine ⟨h1, h2, fun m γ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc' => ?_⟩
    obtain ⟨b, a, v, u, -, hv, hcov, -, -, hvl, hoff, -⟩ := hφc X hX m γ hγ
    have inv : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → InRCone γ β → InRCone v β := by
      intro β hβ hp hw1 hc
      by_contra hn
      have := hoff β hβ hp (inRCone_trans hcov hc) hn
      rw [h3 β hβ hp hw1] at this
      exact lt_irrefl _ this
    exact h4 b v hv hvl β hβ hp β' hβ' hp' hw1 hw2 (inv β hβ hp hw1 hc) (inv β' hβ' hp' hw2 hc')
  obtain ⟨φ', hp', ht', hsub, hs1, hs2, hs3⟩ := GlobalTheory.T.exists_starSubdivision_invariant_polyhedral_fan E H q φ w hdom hφp hφt hwt hcen
  refine ⟨φ', ht', hp', hsub.trans hφs, fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw X hX
  have hnat : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n :=
    fun β hβ hp => ⟨_, hcar X hX β hβ hp⟩
  have core : ∀ (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X),
      IsCell H.bar φ (Fin.append v u) → IsCell H.bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) →
      (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) →
      (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) →
      (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β →
        ((i + 1 : ℕ) : ℝ) < lab.evalZ β) →
      (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) →
      ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone (Fin.append v u) β₀ →
      ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
        IsFaceCut (Fin.append v u) s h → 0 < h β₀ →
      ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X),
        IsCell H.bar φ' (Fin.append v' u') ∧ IsCell H.bar ψ v' ∧
        (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → _) k)) ∧
        Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧
        (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧
        (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β →
          (i : ℝ) < lab.evalZ β) ∧
        ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
    intro b a v u hγ hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0
    exact GlobalTheory.T.starSubdivision_barycentre_cell_next_stage (𝓞 E) H.bar ψ lab φ' w i X b a v u hv hinj hlu hvl hoff hind hnat
      (fun m' s h hh => GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell E H q ψ hψ X hX (hdom X) b v hv m' s h hh) h5
      (fun β hβ hp β' hβ' hp' hw1 hw2 hc hc' => (hcen X hX).2.2 _ _ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc')
      (fun β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e =>
        GlobalTheory.T.carrierDim_le_of_add_cell_generators (𝓞 E) H.bar q ψ lab hcar X hX b v hv β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e)
      β₀ hb0 hp0 hw0 (h3 β₀ hb0 hp0 hw0) hin0
      (fun m' s h hh hpos => hs2 X hX _ _ hγ β₀ hb0 hp0 hw0 hin0 m' s h hh hpos)
  rcases hs3 X hX n γ' hγ' with ⟨m, γ, hγ, hno, hcov'⟩ | ⟨m, δ, β₀, m', s, h, hδ, hb0, hp0, hw0, hin0, hcut, hpos, hcov'⟩
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m γ hγ
    by_cases hc : ∃ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone (Fin.append v u) β₀
    · obtain ⟨β₀, hb0, hp0, hw0, hin0⟩ := hc
      have hnin : ¬ InRCone γ β₀ := fun hh => by
        have := hno β₀ hb0 hp0 hh
        rw [hw0] at this
        exact one_ne_zero this
      obtain ⟨m', s, h, hcut, hpos, hsub'⟩ := reduce_of_not_mem hG hγ hcov hb0 hp0 hin0 hnin
      obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
        core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0 m' s h hcut hpos
      exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_cons_of (n := 0) β₀
        (inRCone_trans hsub' (hcov' j))), r4, r5, r6, r7, r8⟩
    · push_neg at hc
      have hw0 : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → w.evalZ β = 0 :=
        fun β hβ hp hin => (h1 β hβ hp).resolve_right fun e => hc β hβ hp e hin
      refine ⟨b, a, v, u, hs1 X hX _ _ hG hw0, hv, fun j => inRCone_trans hcov (hcov' j), hinj,
        fun j => ?_, fun β hβ hp hin => ?_, fun β hβ hp hin hn => ?_, hind⟩
      · have := hlu j; push_cast at this ⊢; linarith
      · obtain ⟨k, hk⟩ := hnat β hβ hp
        have hle := hvl β hβ hp hin
        rw [hk] at hle ⊢
        have hle' : k ≤ i + 1 := by exact_mod_cast hle
        rcases hle'.lt_or_eq with hl | hl
        · exact_mod_cast Nat.lt_succ_iff.1 hl
        · obtain ⟨β₁, hb1, hp1, hw1, hin1⟩ := h5 b v hv β hβ hp hin (by rw [hk, hl])
          exact absurd (inRCone_append_left v u hin1) (hc β₁ hb1 hp1 hw1)
      · have := hoff β hβ hp hin hn; push_cast at this ⊢; linarith
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m δ hδ
    obtain ⟨m'', s', h', hcut', hpos', hsub'⟩ := reduce_of_mem hG hδ hcov hin0 hcut hpos
    obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
      core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 (inRCone_trans hcov hin0) m'' s' h' hcut' hpos'
    exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_trans (inRCone_cons_mono β₀ hsub') (hcov' j)),
      r4, r5, r6, r7, r8⟩

end GlobalTheory.PolFan
end
end
