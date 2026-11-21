import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryAdmissibleFiniteMultiplicity
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpanRangeEqTopOfIsIrreducible
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupIrreducibleOfAdmissibleUnitary
import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsOpenIsCompactSubgroupFiniteAdelicUnitary
import Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalAutomorphicFormsUnitaryOfTypeLe
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AutTranslate

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S] [Module ℂ S]

private def eqForms (ρ : Representation ℂ (infU E n) S) : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩

private noncomputable def eqRep (ρ : Representation ℂ (infU E n) S) : Representation ℂ (finU E n) (eqForms ρ) where
  toFun k := (LinearMap.llcomp ℂ _ _ _ (RU E n k)).restrict (p := eqForms ρ) (q := eqForms ρ) fun f h =>
    ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
      change RU E n k (f (ρ x v)) = RU E n x (RU E n k (f v))
      rw [h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩
  map_one' := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g => congrArg (f.1 v) (mul_one g))
  map_mul' a b := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g =>
    congrArg (f.1 v) (mul_assoc g a b).symm)

private theorem eqRep_adm [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (f : eqForms ρ) :
    ∃ K : Subgroup (finU E n), (∀ k ∈ K, eqRep ρ k f = f) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed (eqRep ρ) K) ∧
      ∀ w, (Set.range fun k : K => eqRep ρ k w).Finite :=
  _root_.UpperTheory.Reformulated.B.Gr38.eqRep_adm ρ f

end

theorem UpperTheory.admissible_equivariantForms_representation :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → B φ φ = 0 → φ = 0) → (∀ x φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n x φ) (RU E n x ψ) = B φ ψ) → ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ f : S →ₗ[ℂ] (UA E n → ℂ), (∀ v, IsAutFormU (f v)) → (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → ∀ v, f v ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1 := by
  intro E _ _ _ n B hdefB hinv S _ _ _ ρ hsp f hfa hfe v
  classical
  by_cases hv : v = 0
  · rw [hv, map_zero]
    exact zero_mem _
  let ev : eqForms ρ →ₗ[ℂ] (UA E n → ℂ) := LinearMap.applyₗ v ∘ₗ (eqForms ρ).subtype
  let B' : eqForms ρ →ₗ⋆[ℂ] eqForms ρ →ₗ[ℂ] ℂ := (B.compl₂ ev).comp ev
  have hB' : ∀ u w, B' u w = B (u.1 v) (w.1 v) := fun _ _ => rfl
  have hev : ∀ u : eqForms ρ, u.1 v = 0 → u = 0 := fun u hu => by
    have h1 : ∀ T ∈ Submodule.span ℂ (Set.range ρ), u.1 (T v) = 0 := by
      intro T hT
      induction hT using Submodule.span_induction with
      | mem T hT =>
        obtain ⟨x, rfl⟩ := hT
        rw [u.2.2, hu, map_zero]
      | zero => simp
      | add a b _ _ ha hb => rw [LinearMap.add_apply, map_add, ha, hb, add_zero]
      | smul c a _ ha => rw [LinearMap.smul_apply, map_smul, ha, smul_zero]
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hv
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    have h2 := h1 (LinearMap.smulRight l w) (hsp ▸ Submodule.mem_top)
    rw [LinearMap.smulRight_apply, hl, one_smul] at h2
    exact h2
  have hdef : ∀ u, B' u u = 0 → u = 0 := fun u hu => hev u (hdefB _ (u.2.1 v) hu)
  have hinv' : ∀ g u w, B' (eqRep ρ g u) (eqRep ρ g w) = B' u w := fun g u w =>
    hinv g _ _ (u.2.1 _) (w.2.1 _)
  have hmem := UpperTheory.mem_iSup_irreducible_of_admissible_unitary (finU E n) (eqForms ρ) (eqRep ρ) B' hdef hinv' (eqRep_adm ρ) ⟨f, hfa, hfe⟩
  refine (iSup_le ?_ : _ ≤ (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1).comap ev) hmem
  rintro ⟨U, hU0, hU, hirr⟩
  let j : U →ₗ[ℂ] S →ₗ[ℂ] (UA E n → ℂ) := (eqForms ρ).subtype ∘ₗ U.subtype
  have hj : ∀ (p : U) (x : infU E n) v, j p (ρ x v) = RU E n x.1 (j p v) := fun p x v => p.1.2.2 x v
  have hrep : IsAutRepU (Pairs.img j) := by
    refine ⟨fun φ hφ => ?_, fun x φ hφ => ?_, fun h => hU0 ?_, fun N hle hN => ?_⟩
    · have h1 : Pairs.img j ≤ autU E n := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        exact p.1.2.1 v)
      exact h1 hφ
    · refine Pairs.stable_of (fun a => ?_) (fun k => ?_) x φ hφ
      · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n a.1) := Submodule.span_le.2 (by
          rintro _ ⟨p, v, rfl⟩
          change RU E n a.1 _ ∈ Pairs.img j
          rw [← hj]
          exact Pairs.apply_mem_img _ _ _)
        exact fun φ hφ => h1 hφ
      · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n k.1) := Submodule.span_le.2 (by
          rintro _ ⟨p, v, rfl⟩
          exact Pairs.apply_mem_img j ⟨eqRep ρ k p.1, hU k _ p.2⟩ v)
        exact fun φ hφ => h1 hφ
    · rw [Submodule.eq_bot_iff]
      intro u hu
      have := Pairs.apply_mem_img j ⟨u, hu⟩ v
      rw [h, Submodule.mem_bot] at this
      exact hev u this
    · refine Pairs.eq_bot_or_eq_img hsp (R := fun x => RU E n x.1) hj
        (Q := fun k : finU E n => (eqRep ρ k).restrict (hU k)) (T := fun k => RU E n k.1) (fun _ _ _ => rfl)
        (fun P hP => ?_) hle (fun x => hN x.1) (fun k => hN k.1)
      rcases hirr (P.map U.subtype) (Submodule.map_subtype_le U P) (by
        rintro g _ ⟨p, hp, rfl⟩
        exact ⟨_, hP g p hp, rfl⟩) with h | h
      · left
        exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_bot _).symm)
      · right
        exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_subtype_top _).symm)
  intro u hu
  exact le_iSup (fun σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ} => σ.1) ⟨_, hrep⟩
    (Pairs.apply_mem_img j ⟨u, hu⟩ v)
end

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

theorem UpperTheory.mem_iSup_automorphicReps_of_invariant_form :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → B φ φ = 0 → φ = 0) → (∀ x φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n x φ) (RU E n x ψ) = B φ ψ) → ∀ φ : UA E n → ℂ, IsAutFormU φ → φ ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1 := by
  intro E _ _ _ n B hdef hinv φ hφ
  classical
  haveI : FiniteDimensional ℂ (admitted.X φ) := hφ.kfin
  have hXA : admitted.X φ ≤ autU E n := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact RU_mem_autU _ _ (mem_autU.2 hφ))
  have haut : ∀ v : admitted.X φ, IsAutFormU (v : UA E n → ℂ) := fun v => mem_autU.1 (hXA v.2)
  let Z : Subrepresentation ((RU E n).comp (infU E n).subtype) :=
    ⟨admitted.X φ, fun g v hv => admitted.RU_mem_X φ g hv⟩
  let ρ : Representation ℂ (infU E n) (admitted.X φ) := Z.toRepresentation
  have hρ : ∀ g (v : admitted.X φ), ((ρ g v : admitted.X φ) : UA E n → ℂ) = RU E n g v := fun _ _ => rfl
  let B' : admitted.X φ →ₗ⋆[ℂ] admitted.X φ →ₗ[ℂ] ℂ := (B.comp (admitted.X φ).subtype).compl₂ (admitted.X φ).subtype
  have hx := UpperTheory.mem_iSup_irreducible_of_admissible_unitary (infU E n) (admitted.X φ) ρ B'
    (fun v hv => Subtype.ext (hdef _ (haut v) hv))
    (fun g u v => hinv g _ _ (haut u) (haut v))
    (fun v => ⟨⊥, fun k hk => by rw [Subgroup.mem_bot.1 hk, map_one]; rfl, inferInstance,
      fun w => Set.finite_range _⟩)
    ⟨φ, admitted.self_mem_X φ⟩
  have hle : (⨆ U : {U : Submodule ℂ (admitted.X φ) // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
      ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) ≤
      (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1).comap (admitted.X φ).subtype := by
    refine iSup_le ?_
    rintro ⟨U, h0, hst, hirr⟩ u hu
    let Y : Subrepresentation ρ := ⟨U, fun g v hv => hst g v hv⟩
    let τ : Representation ℂ (infU E n) U := Y.toRepresentation
    have hτ : τ.IsIrreducible := by
      refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨Submodule.nontrivial_iff_ne_bot.2 h0, fun N hN => ?_⟩
      rcases hirr (N.map U.subtype) (Submodule.map_subtype_le _ _) (by
        rintro g _ ⟨w, hw, rfl⟩
        exact ⟨τ g w, hN g w hw, rfl⟩) with h | h
      · left
        exact Submodule.map_injective_of_injective U.injective_subtype (by rw [h, Submodule.map_bot])
      · right
        exact Submodule.map_injective_of_injective U.injective_subtype
          (by rw [h, Submodule.map_top, Submodule.range_subtype])
    exact UpperTheory.admissible_equivariantForms_representation E n B hdef hinv U τ
      (GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ τ hτ)
      ((admitted.X φ).subtype ∘ₗ U.subtype) (fun v => haut v.1) (fun _ _ => rfl) ⟨u, hu⟩
  exact hle hx
end
