import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

section
open Formalism.REAL

namespace GlobalTheory

inductive LoweringWord {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : ℕ → V → Prop
  | base : LoweringWord E v 0 v
  | step {N : ℕ} {x : V} (a b : Fin n) (h : b < a) :
      LoweringWord E v N x → LoweringWord E v (N + (a.val - b.val)) (E a b x)

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
  {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℂ} {v : V}

theorem glRel_apply_comm (hE : GlRel E) (a b c d : Fin n) (y : V) :
    E a b (E c d y) = E c d (E a b y) + (if b = c then E a d y else 0)
      - (if d = a then E c b y else 0) := by
  have h := congrArg (fun f : Module.End ℂ V => f y) (hE a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h1 : (if b = c then E a d else 0) y = if b = c then E a d y else 0 := by
    split_ifs <;> simp
  have h2 : (if d = a then E c b else 0) y = if d = a then E c b y else 0 := by
    split_ifs <;> simp
  rw [h1, h2] at h
  rw [add_sub_assoc, ← h]
  abel

theorem loweringWord_span_lower (a b : Fin n) (hab : b < a) :
    ∀ x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x},
      E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨N, hN⟩ := hx
    exact Submodule.subset_span ⟨_, hN.step a b hab⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem loweringWord_apply_mem (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    ∀ a b, E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  induction hx with
  | base =>
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hv.2 a b h]; exact Submodule.zero_mem _
    · subst h
      rw [hv.1 a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, LoweringWord.base⟩)
    · exact Submodule.subset_span ⟨_, LoweringWord.base.step a b h⟩
  | step c d h _ ih =>
    intro a b
    rw [glRel_apply_comm hE]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (loweringWord_span_lower c d h _ (ih a b)) ?_) ?_
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _

theorem loweringWord_height (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) x
      = ((∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a) + (N : ℂ)) • x := by
  induction hx with
  | base =>
    simp [LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
  | @step N y c d h _ ih =>
    have key : (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) (E c d y)
        = E c d ((∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) y)
          + ((c.val : ℕ) : ℂ) • E c d y - ((d.val : ℕ) : ℂ) • E c d y := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      simp only [glRel_apply_comm hE _ _ c d y, smul_sub, smul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [key, ih, map_smul]
    have hle : d.val ≤ c.val := le_of_lt h
    push_cast [Nat.cast_sub hle]
    module

theorem loweringWord_zero_or_pos {N : ℕ} {x : V} (hx : LoweringWord E v N x) :
    x = v ∨ 0 < N := by
  cases hx with
  | base => exact Or.inl rfl
  | step c d h _ =>
    right
    have : d.val < c.val := h
    omega

end

theorem exists_stable_submodule_topWeight_line :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
      (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
      ∃ S : Submodule ℂ V, (∀ a b, ∀ x ∈ S, E a b x ∈ S) ∧ v ∈ S ∧
        ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v := by
  intro V _ _ n E ν v hE hv
  refine ⟨Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}, ?_,
    Submodule.subset_span ⟨0, LoweringWord.base⟩, ?_⟩
  · intro a b x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨N, hN⟩ := hx
      exact loweringWord_apply_mem hE hv hN a b
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · intro x hx hw
    set H : Module.End ℂ V := ∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a with hH
    set h : ℂ := ∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a with hh
    have hle : Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}
        ≤ Submodule.span ℂ {v} ⊔ ⨆ (μ : ℂ) (_ : μ ≠ h), H.eigenspace μ := by
      rw [Submodule.span_le]
      rintro y ⟨N, hN⟩
      rcases loweringWord_zero_or_pos hN with rfl | hpos
      · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      · refine Submodule.mem_sup_right ?_
        have hne : h + (N : ℂ) ≠ h := by
          have : (N : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
          simpa using this
        refine Submodule.mem_iSup_of_mem (h + (N : ℂ)) (Submodule.mem_iSup_of_mem hne ?_)
        rw [Module.End.mem_eigenspace_iff]
        exact loweringWord_height hE hv hN
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hxe : x ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hw, Finset.sum_smul, mul_smul]
    have hve : v ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
    have hze : z ∈ H.eigenspace h := by
      have : z = x - c • v := by rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hxe (Submodule.smul_mem _ _ hve)
    have hd := Module.End.eigenspaces_iSupIndep H h
    have hz0 : z = 0 := (Submodule.disjoint_def.1 hd) z hze hz
    exact ⟨c, by rw [← hyz, hz0, add_zero]⟩

end GlobalTheory
end

section
open Formalism.REAL

namespace GlobalTheory

theorem stable_submodule_proj_bijective {U V₁ V₂ : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ U) (E₁ : Fin n → Fin n → Module.End ℂ V₁)
    (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v : U)
    (p : U →ₗ[ℂ] V₁) (q : U →ₗ[ℂ] V₂)
    (hp : ∀ a b x, p (E a b x) = E₁ a b (p x)) (hq : ∀ a b x, q (E a b x) = E₂ a b (q x))
    (hpq : ∀ x, p x = 0 → q x = 0 → x = 0)
    (h₁ : ∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (h₂ : ∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hw : ∀ a, E₁ a a (p v) = ν a • p v) (hv₁ : p v ≠ 0) (hv₂ : q v ≠ 0)
    (S : Submodule ℂ U) (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (hvS : v ∈ S)
    (htop : ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v) :
    Function.Bijective (q.comp S.subtype) := by
  constructor
  · have hK := h₁ ((S ⊓ LinearMap.ker q).map p) (by
      rintro a b _ ⟨x, ⟨hxS, hxq⟩, rfl⟩
      refine ⟨E a b x, ⟨hS a b x hxS, ?_⟩, hp a b x⟩
      have hxq' : q x = 0 := hxq
      show q (E a b x) = 0
      rw [hq, hxq', map_zero])
    rcases hK with hK | hK
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have hx' : q x = 0 := hx
      have hm : p x ∈ (S ⊓ LinearMap.ker q).map p := ⟨x, ⟨x.2, hx'⟩, rfl⟩
      rw [hK, Submodule.mem_bot] at hm
      exact Subtype.ext (hpq _ hm hx')
    · exfalso
      have hm : p v ∈ (S ⊓ LinearMap.ker q).map p := by rw [hK]; trivial
      obtain ⟨x, ⟨hxS, hxq⟩, hxp⟩ := hm
      have hxq' : q x = 0 := hxq
      obtain ⟨c, hc⟩ := htop x hxS (fun a => by
        rw [← sub_eq_zero]
        apply hpq
        · rw [map_sub, hp, map_smul, hxp, hw, sub_self]
        · rw [map_sub, hq, map_smul, hxq', map_zero, smul_zero, sub_self])
      rw [hc, map_smul, smul_eq_zero] at hxq'
      rcases hxq' with h0 | h0
      · apply hv₁
        rw [← hxp, hc, h0, zero_smul, map_zero]
      · exact hv₂ h0
  · have hK := h₂ (S.map q) (by
      rintro a b _ ⟨x, hxS, rfl⟩
      exact ⟨E a b x, hS a b x hxS, hq a b x⟩)
    rcases hK with hK | hK
    · exfalso
      have hm : q v ∈ S.map q := ⟨v, hvS, rfl⟩
      rw [hK, Submodule.mem_bot] at hm
      exact hv₂ hm
    · intro y
      have hm : y ∈ S.map q := by rw [hK]; trivial
      obtain ⟨x, hxS, rfl⟩ := hm
      exact ⟨⟨x, hxS⟩, rfl⟩

theorem exists_linearEquiv_of_irreducible_isHW :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁) (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v₁ : V₁) (v₂ : V₂), GlRel E₁ → GlRel E₂ → (∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → IsHW E₁ ν v₁ → IsHW E₂ ν v₂ → v₁ ≠ 0 → v₂ ≠ 0 → ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by
  intro V₁ _ _ V₂ _ _ n E₁ E₂ ν v₁ v₂ hE₁ hE₂ h₁ h₂ hw₁ hw₂ hv₁ hv₂
  let E : Fin n → Fin n → Module.End ℂ (V₁ × V₂) := fun a b => (E₁ a b).prodMap (E₂ a b)
  have hEap : ∀ a b (x : V₁ × V₂), E a b x = (E₁ a b x.1, E₂ a b x.2) := fun _ _ _ => rfl
  have hE : GlRel E := by
    intro a b c d
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hEap]
    rw [glRel_apply_comm hE₁ a b c d, glRel_apply_comm hE₂ a b c d]
    split_ifs <;> simp [hEap]
    all_goals (constructor <;> abel)
  have hw : IsHW E ν (v₁, v₂) := by
    refine ⟨fun a => ?_, fun a b h => ?_⟩
    · rw [hEap, hw₁.1, hw₂.1]; rfl
    · rw [hEap, hw₁.2 a b h, hw₂.2 a b h]; rfl
  obtain ⟨S, hS, hvS, htop⟩ := exists_stable_submodule_topWeight_line _ n E ν _ hE hw
  have b₂ := stable_submodule_proj_bijective E E₁ E₂ ν (v₁, v₂) (LinearMap.fst ℂ V₁ V₂)
    (LinearMap.snd ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h h') h₁ h₂ hw₁.1 hv₁ hv₂ S hS hvS htop
  have b₁ := stable_submodule_proj_bijective E E₂ E₁ ν (v₁, v₂) (LinearMap.snd ℂ V₁ V₂)
    (LinearMap.fst ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h' h) h₂ h₁ hw₂.1 hv₂ hv₁ S hS hvS htop
  refine ⟨(LinearEquiv.ofBijective _ b₁).symm.trans (LinearEquiv.ofBijective _ b₂), ?_⟩
  intro a b x
  obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ b₁).surjective x
  have h : E₁ a b (LinearEquiv.ofBijective _ b₁ y)
      = LinearEquiv.ofBijective _ b₁ ⟨E a b y, hS a b y y.2⟩ := rfl
  rw [h]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory
end
