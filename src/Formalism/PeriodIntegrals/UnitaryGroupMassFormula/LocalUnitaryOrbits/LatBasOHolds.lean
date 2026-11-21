import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUnifOIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfBas

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

section Bas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem basRatV_add (x y : Fin n → E) :
    ratV (F := F) (Fv F v) (x + y) = ratV (F := F) (Fv F v) x + ratV (F := F) (Fv F v) y := by
  funext i
  simp [ratV, map_add]

theorem basRatV_zsmul (c : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (c • x) = c • ratV (F := F) (Fv F v) x := by
  funext i
  simp [ratV]

theorem basRatV_zero : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
  funext i
  simp [ratV]

theorem basRatV_single (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e : Fin n → E) =
      (Pi.single i (inclR (F := F) (Fv F v) e) : Fin n → Fv F v ⊗[F] E) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ratV]
  · simp [ratV, Pi.single_eq_of_ne h]

theorem basInt_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ y • x ∈ L := by
  classical
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  obtain ⟨m, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  convert L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1
  rw [← smul_assoc]
  rfl

theorem basLat_fg (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsLattice E L) :
    (latLoc (E := E) v (L : Set (Fin n → E))).FG := by
  classical
  obtain ⟨s, hs⟩ : (L.restrictScalars ℤ).FG := hLat.fg.restrictScalars
  refine ⟨s.image (ratV (F := F) (Fv F v)), ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxL : x ∈ L := by
      have : x ∈ L.restrictScalars ℤ := by
        rw [← hs]
        exact Submodule.subset_span hx
      exact this
    exact Submodule.subset_span ⟨x, hxL, rfl⟩
  · unfold latLoc
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span ℤ (s : Set (Fin n → E)) := by
      rw [hs]
      exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      rw [basRatV_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [basRatV_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [basRatV_zsmul]
      exact zsmul_mem hy c

theorem basSpan_top (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsLattice E L) :
    Submodule.span (Fv F v) (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) = ⊤ := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let bE := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (Fv F v) bE
  let P := Pi.basis (fun _ : Fin n => B)
  rw [eq_top_iff, ← P.span_eq, Submodule.span_le]
  rintro _ ⟨⟨i, k⟩, rfl⟩
  obtain ⟨N, hN, hNL⟩ := basInt_smul_mem L hLat.span_eq_top (Pi.single i (bE k) : Fin n → E)
  have hN' : (N : Fv F v) ≠ 0 := by
    rw [← map_intCast (algebraMap F (Fv F v))]
    exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hN)
  have hmem : ratV (F := F) (Fv F v) (N • (Pi.single i (bE k) : Fin n → E)) ∈
      latLoc (E := E) v (L : Set (Fin n → E)) := Submodule.subset_span ⟨_, hNL, rfl⟩
  have e : P ⟨i, k⟩ = (N : Fv F v)⁻¹ • ratV (F := F) (Fv F v) (N • (Pi.single i (bE k) : Fin n → E)) := by
    rw [basRatV_zsmul, basRatV_single, ← Int.cast_smul_eq_zsmul (Fv F v), smul_smul, inv_mul_cancel₀ hN', one_smul]
    simp only [P, B, Pi.basis_apply, Algebra.TensorProduct.basis_apply]
    rfl
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end Bas

end PI.OmLocU
end
end

section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem exists_basO (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsLattice E L) :
    ∃ (m : ℕ) (b : Fin m → Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
      (∀ x, x ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        ∃ c : Fin m → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i) ∧
      ⊤ ≤ Submodule.span (Fv F v) (Set.range b) := by
  classical
  set M := latLoc (E := E) v (L : Set (Fin n → E)) with hM
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 (basLat_fg v L hLat)
  have : Module.IsTorsionFree (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      have h' : (r : Fv F v) • x = 0 := h
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr h0
  have : Module.Free (v.adicCompletionIntegers F) M := Module.free_of_finite_type_torsion_free'
  let bM := Module.finBasis (v.adicCompletionIntegers F) M
  let b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fin n → Fv F v ⊗[F] E := fun i => (bM i : _)
  have hli0 : LinearIndependent (v.adicCompletionIntegers F) b0 :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent (Fv F v) b0 :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0
  have hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • b0 i := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2
  refine ⟨_, b0, hli, hmem, ?_⟩
  rw [← basSpan_top v L hLat, Submodule.span_le]
  intro x hx
  obtain ⟨c, rfl⟩ := (hmem x).1 hx
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem latBasO_holds (a : ℕ) (Y : TupV (E := E) v n a) : LatBasO σ J ψ v Λ a Y := by
  classical
  rintro ⟨⟨hCM, -⟩, ⟨L, hLat, rfl⟩, -⟩
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩


end PI.OmLocU
end
end
