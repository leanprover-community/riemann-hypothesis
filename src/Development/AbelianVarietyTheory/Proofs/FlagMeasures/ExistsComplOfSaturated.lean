import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

section
namespace GlobalTheory.SaturatedSublatticeComplement

universe u_1 u_2

open Module

theorem saturated_has_complement {R : Type u_1} {V : Type u_2} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup V] [Module R V] (N M : Submodule R V) (hNM : N ≤ M) (hM : M.FG)
    (hsat : ∀ (r : R) (y : V), r ≠ 0 → y ∈ M → r • y ∈ N → y ∈ N) :
    ∃ A : Submodule R V, A ⊓ N = ⊥ ∧ A ⊔ N = M := by
  classical
  let N' : Submodule R M := N.comap M.subtype
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  haveI : IsTorsionFree R (M ⧸ N') := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r q hq
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨m, rfl⟩ := N'.mkQ_surjective q
    have h1 : r • m ∈ N' := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa using hq
    have h2 : (m : V) ∈ N := hsat r m hr m.2 (by simpa [N'] using h1)
    exact (Submodule.Quotient.mk_eq_zero N').mpr (by simpa [N'] using h2)
  haveI : Module.FinitePresentation R (M ⧸ N') := Module.finitePresentation_of_finite R _
  haveI : Module.Projective R (M ⧸ N') := Module.Flat.projective_of_finitePresentation
  obtain ⟨g, hg⟩ := Module.projective_lifting_property N'.mkQ LinearMap.id N'.mkQ_surjective
  have hg' : ∀ q, N'.mkQ (g q) = q := fun q => LinearMap.congr_fun hg q
  refine ⟨(LinearMap.range g).map M.subtype, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxA, hxN⟩
    obtain ⟨_, ⟨q, rfl⟩, rfl⟩ := hxA
    have hmem : g q ∈ N' := by simpa [N'] using hxN
    have hq0 : q = 0 := by
      rw [← hg' q]
      exact (Submodule.Quotient.mk_eq_zero N').mpr hmem
    simp [hq0]
  · apply le_antisymm
    · exact sup_le (by
        rintro x ⟨y, -, rfl⟩
        exact y.2) hNM
    · intro x hx
      let m : M := ⟨x, hx⟩
      have hd : m - g (N'.mkQ m) ∈ N' := by
        rw [← Submodule.Quotient.mk_eq_zero]
        have := hg' (N'.mkQ m)
        simp only [Submodule.mkQ_apply] at this ⊢
        rw [Submodule.Quotient.mk_sub, this, sub_self]
      have hx' : x = (g (N'.mkQ m) : V) + ((m - g (N'.mkQ m) : M) : V) := by simp [m]
      rw [hx']
      exact Submodule.add_mem_sup ⟨g (N'.mkQ m), ⟨_, rfl⟩, rfl⟩ (by simpa [N'] using hd)

theorem main : ∀ {R : Type u_1} {V : Type u_2} [inst : CommRing R] [IsDedekindDomain R]
    [inst_2 : AddCommGroup V] [inst_3 : Module R V] (N M : Submodule R V), N ≤ M →
    Submodule.FG M → (∀ (r : R) (y : V), r ≠ (0 : R) → y ∈ M → r • y ∈ N → y ∈ N) →
    ∃ (A : Submodule R V), A ⊓ N = ⊥ ∧ A ⊔ N = M :=
  fun N M h1 h2 h3 => saturated_has_complement N M h1 h2 h3

end GlobalTheory.SaturatedSublatticeComplement
end

section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem exists_compl_of_saturated {R V : Type*} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup V] [Module R V] (N M : Submodule R V) (hNM : N ≤ M) (hM : M.FG)
    (hsat : ∀ (r : R) (y : V), r ≠ 0 → y ∈ M → r • y ∈ N → y ∈ N) :
    ∃ A : Submodule R V, A ⊓ N = ⊥ ∧ A ⊔ N = M := by
  first
  | exact @_root_.GlobalTheory.SaturatedSublatticeComplement.main
  | exact _root_.GlobalTheory.SaturatedSublatticeComplement.main
  | (apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedSublatticeComplement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedSublatticeComplement.main ..)

theorem saturatedFlag_splits : ∀ (E : Type) [Field E] [NumberField E] (n a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 E) (Fin n → E)), S 0 = ⊥ → Monotone S → (S (Fin.last a)).FG → (∀ i, ∀ y ∈ S (Fin.last a), y ∈ Submodule.span E (S i : Set (Fin n → E)) → y ∈ S i) → ∃ A : Fin a → Submodule (𝓞 E) (Fin n → E), ∀ i, A i ⊓ S i.castSucc = ⊥ ∧ A i ⊔ S i.castSucc = S i.succ := by
  intro E _ _ n a S _ hmono hfg hsat
  have key : ∀ i : Fin a, ∃ A : Submodule (𝓞 E) (Fin n → E),
      A ⊓ S i.castSucc = ⊥ ∧ A ⊔ S i.castSucc = S i.succ := by
    intro i
    have hle : S i.succ ≤ S (Fin.last a) := hmono (Fin.le_last _)
    refine exists_compl_of_saturated _ _ (hmono (Fin.castSucc_lt_succ).le)
      (Submodule.FG.of_le hfg hle) ?_
    intro r y hr hy hry
    apply hsat _ y (hle hy)
    have hr' : (algebraMap (𝓞 E) E r) ≠ 0 := by
      simpa using hr
    have : y = (algebraMap (𝓞 E) E r)⁻¹ • (r • y) := by
      rw [← algebraMap_smul E r y, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hry)
  choose A hA using key
  exact ⟨A, hA⟩

end GlobalTheory
end
