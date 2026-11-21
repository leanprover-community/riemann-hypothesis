import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSlowlyIncreasing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorCompactFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGLAdelicProjectionsInclusionsStatement

section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_compact_finiteAdeles : ∀ (E : Type) [Field E] [NumberField E] (Kf : Set (Af E)), IsCompact Kf → ∃ n : ℕ, 0 < n ∧ ∀ ξ : E, algebraMap E (Af E) ξ ∈ Kf → IsIntegral ℤ ((n : E) * ξ) := by
  first | exact @GlobalTheory.AdeleDenom.exists_common_denom | exact GlobalTheory.AdeleDenom.exists_common_denom | (intros; apply GlobalTheory.AdeleDenom.exists_common_denom <;> assumption)
end

section
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory.IntCount

theorem exists_abs_repr_le_mul_house (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)),
      |(((RingOfIntegers.basis E).repr x j : ℤ) : ℝ)| ≤ C * house (x : E) := by
  let L := (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap.toContinuousLinearMap
  refine ⟨‖L‖, norm_nonneg _, fun x j => ?_⟩
  have h1 := L.le_opNorm (canonicalEmbedding E x)
  have h2 := norm_le_pi_norm (L (canonicalEmbedding E x)) j
  have h3 : L (canonicalEmbedding E x) j = (((RingOfIntegers.basis E).repr x j : ℤ) : ℂ) := by
    have := canonicalEmbedding.integralBasis_repr_apply E (x : E) j
    rw [NumberField.integralBasis_repr_apply] at this
    simpa [L] using this
  rw [h3, Complex.norm_intCast] at h2
  exact h2.trans h1

theorem card_bounded_integers_le (E : Type) [Field E] [NumberField E] :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.Finite ∧
      ({ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.ncard : ℝ) ≤ C * T ^ m := by
  classical
  obtain ⟨c, hc, hb⟩ := exists_abs_repr_le_mul_house E
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  refine ⟨Fintype.card ι, (2 * c + 3) ^ Fintype.card ι, by positivity, fun T hT => ?_⟩
  set S := {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T} with hS
  let M : ℕ := ⌈c * T⌉₊
  let s : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M
  let f : 𝓞 E → (ι → ℤ) := fun ξ j => (RingOfIntegers.basis E).repr ξ j
  have hf : Function.Injective f := fun ξ η h =>
    (RingOfIntegers.basis E).ext_elem fun j => congrFun h j
  have hmaps : ∀ ξ ∈ S, f ξ ∈ s := by
    intro ξ hξ
    refine Fintype.mem_piFinset.2 fun j => Finset.mem_Icc.2 (abs_le.1 ?_)
    have hh : house (ξ : E) ≤ T := by
      refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun φ => ?_
      have := hξ (InfinitePlace.mk φ)
      rwa [InfinitePlace.apply] at this
    have h1 := hb ξ j
    have h2 : c * house (ξ : E) ≤ (M : ℝ) :=
      (mul_le_mul_of_nonneg_left hh hc).trans (Nat.le_ceil _)
    exact_mod_cast h1.trans h2
  have hsub : S ⊆ f ⁻¹' (s : Set (ι → ℤ)) := fun ξ hξ => hmaps ξ hξ
  have hfin : S.Finite := ((s.finite_toSet).preimage hf.injOn).subset hsub
  refine ⟨hfin, ?_⟩
  have hcard : S.ncard ≤ s.card := by
    rw [← Set.ncard_coe_finset s]
    exact Set.ncard_le_ncard_of_injOn f (fun ξ hξ => hmaps ξ hξ) hf.injOn s.finite_toSet
  have hs : (s.card : ℝ) = (2 * (M : ℝ) + 1) ^ Fintype.card ι := by
    simp only [s, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
    push_cast
    congr 1
    have : (↑M + 1 - -↑M : ℤ).toNat = 2 * M + 1 := by omega
    rw [this]; push_cast; ring
  have hM : (M : ℝ) ≤ c * T + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hbase : 2 * (M : ℝ) + 1 ≤ (2 * c + 3) * T := by nlinarith
  calc (S.ncard : ℝ) ≤ s.card := by exact_mod_cast hcard
    _ = (2 * (M : ℝ) + 1) ^ Fintype.card ι := hs
    _ ≤ ((2 * c + 3) * T) ^ Fintype.card ι := by gcongr
    _ = (2 * c + 3) ^ Fintype.card ι * T ^ Fintype.card ι := mul_pow _ _ _

end GlobalTheory.IntCount
end

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_algebraic_integers_bounded_archimedean_le : ∀ (E : Type) [Field E] [NumberField E], ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.Finite ∧ ({ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.ncard : ℝ) ≤ C * T ^ m := by
  atlas_forward_decl GlobalTheory.IntCount.card_bounded_integers_le
end

section
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem place_le_norm_pInf {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (ξ : E)
    (w : InfinitePlace E) : w ξ ≤ ‖pInf E (algebraMap E (Ad E) ξ)‖ := by
  have h := norm_le_pi_norm (pInf E (algebraMap E (Ad E) ξ)) w
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq] at h
  exact h

theorem rat_bounded_compact_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], ∃ m : ℕ,
    ∀ Kf : Set (Af E), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.Finite ∧
      ({ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.ncard : ℝ)
        ≤ C * T ^ m := by
  intro E _ _ _
  obtain ⟨m, C₀, hC₀, hcount⟩ := GlobalTheory.T.card_algebraic_integers_bounded_archimedean_le E
  refine ⟨m, fun Kf hKf => ?_⟩
  obtain ⟨n, hn, hint⟩ := GlobalTheory.T.exists_common_denominator_compact_finiteAdeles E Kf hKf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨C₀ * (n : ℝ) ^ m, by positivity, fun T hT => ?_⟩
  have hnT : (1 : ℝ) ≤ n * T := by nlinarith
  obtain ⟨hAfin, hAcard⟩ := hcount (n * T) hnT
  set A := {x : 𝓞 E | ∀ w : InfinitePlace E, w (x : E) ≤ n * T}
  set S := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  have hsub : S ⊆ (fun x : 𝓞 E => (x : E) / n) '' A := by
    intro ξ hξ
    have hi : IsIntegral ℤ ((n : E) * ξ) := hint ξ hξ.2
    refine ⟨⟨(n : E) * ξ, hi⟩, fun w => ?_, ?_⟩
    · show w ((n : E) * ξ) ≤ n * T
      rw [← InfinitePlace.norm_embedding_eq, map_mul, map_natCast, norm_mul, Complex.norm_natCast,
        InfinitePlace.norm_embedding_eq]
      exact mul_le_mul_of_nonneg_left ((place_le_norm_pInf ξ w).trans hξ.1) (Nat.cast_nonneg n)
    · show (n : E) * ξ / n = ξ
      field_simp
  have hSfin : S.Finite := (hAfin.image _).subset hsub
  refine ⟨hSfin, ?_⟩
  have h1 : S.ncard ≤ A.ncard :=
    (Set.ncard_le_ncard hsub (hAfin.image _)).trans (Set.ncard_image_le hAfin)
  calc (S.ncard : ℝ) ≤ A.ncard := by exact_mod_cast h1
    _ ≤ C₀ * (n * T) ^ m := hAcard
    _ = C₀ * (n : ℝ) ^ m * T ^ m := by rw [mul_pow]; ring

end GlobalTheory
end

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], ∃ m : ℕ, ∀ Kf : Set (Af E), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.Finite ∧ ({ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  atlas_forward_decl GlobalTheory.rat_bounded_compact_polynomial
end

section
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem ratGL_bounded_count : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ m : ℕ, ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.Finite ∧ ({γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  intro E _ _ _ a
  obtain ⟨m, hm⟩ := GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount E
  refine ⟨m * (a * a), fun Kf hKf => ?_⟩
  let Kf' : Set (Af E) := ⋃ i : Fin a, ⋃ j : Fin a, (fun g : GL (Fin a) (Af E) => g.val i j) '' Kf
  have hc : IsCompact Kf' := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => hKf.image ?_
    exact (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j
  obtain ⟨C, hC0, hC⟩ := hm Kf' hc
  refine ⟨C ^ (a * a), pow_nonneg hC0 _, fun T hT => ?_⟩
  obtain ⟨hNf, hNc⟩ := hC T hT
  let N : Set E := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf'}
  let S : Set (GL (Fin a) E) := {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}
  change S.Finite ∧ (S.ncard : ℝ) ≤ C ^ (a * a) * T ^ (m * (a * a))
  have hsub : ∀ γ ∈ S, ∀ i j, γ.val i j ∈ N := by
    intro γ hγ i j
    obtain ⟨h1, h2⟩ := hγ
    refine ⟨?_, ?_⟩
    · have he : pInf E (algebraMap E (Ad E) (γ.val i j)) = (toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val) i j := rfl
      rw [he]
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)).trans h1
    · exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨_, h2, rfl⟩⟩⟩
  classical
  let F : Finset E := hNf.toFinset
  let P : Finset (Fin a → Fin a → E) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => F
  let f : GL (Fin a) E → (Fin a → Fin a → E) := fun γ => γ.val
  have hf : Function.Injective f := fun x y h => Units.ext h
  have himg : f '' S ⊆ (P : Set (Fin a → Fin a → E)) := by
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [P, F, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun i j => hsub γ hγ i j
  have hSfin : S.Finite := Set.Finite.of_finite_image ((P.finite_toSet).subset himg) hf.injOn
  refine ⟨hSfin, ?_⟩
  have hcardP : P.card = (F.card ^ a) ^ a := by
    simp [P, Fintype.card_piFinset, Finset.prod_const]
  have hS : S.ncard ≤ (F.card ^ a) ^ a := by
    rw [← Set.ncard_image_of_injective S hf, ← hcardP, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard himg P.finite_toSet
  have hF : (F.card : ℝ) ≤ C * T ^ m := by
    rw [← Set.ncard_eq_toFinset_card N hNf]; exact hNc
  calc (S.ncard : ℝ) ≤ ((F.card ^ a) ^ a : ℕ) := by exact_mod_cast hS
    _ = (F.card : ℝ) ^ (a * a) := by push_cast; rw [← pow_mul]
    _ ≤ (C * T ^ m) ^ (a * a) := pow_le_pow_left₀ (Nat.cast_nonneg _) hF _
    _ = C ^ (a * a) * T ^ (m * (a * a)) := by rw [mul_pow, ← pow_mul]

end GlobalTheory
end

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalGL_boundedSize_compactFinite_polynomialCount : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ m : ℕ, ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.Finite ∧ ({γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  atlas_forward_decl GlobalTheory.ratGL_bounded_count
end

section
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CentralExponent

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.UnitaryBC

theorem abs_le_of_conj_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ W : Set (GA E a), IsCompact W → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (g : GA E a),
      g⁻¹ * (ratGL E a γ * GlobalTheory.UnitaryBC.splitCentre E a 1 ^ n) * g ∈ W → |n| ≤ n₀ := by
  intro E _ _ _ a ha W hW
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  have hc : Continuous fun x : GA E a => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det x)) :=
    (continuous_ideleNorm.comp GeneralLinearGroup.continuous_det).log fun _ => ideleNorm_ne_zero _
  obtain ⟨C, hC⟩ := hW.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊, fun γ n g hmem => ?_⟩
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  have e : GeneralLinearGroup.det (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g) =
      diag E (GeneralLinearGroup.det γ) * eIdele E ^ ((a : ℤ) * n) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_zpow, hd, det_splitCentre_one, ← zpow_natCast, ← _root_.zpow_mul,
      mul_comm _ (GeneralLinearGroup.det g), mul_inv_cancel_left]
  have key : Real.log (ideleNorm (E := E) (GeneralLinearGroup.det
      (g⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * g))) =
      ((a : ℤ) * n : ℤ) * Real.log (ideleNorm (E := E) (eIdele E)) := by
    rw [e, map_mul, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul, map_zpow,
      Real.log_zpow]
  have h1 := hC _ hmem
  rw [key, Real.norm_eq_abs, abs_mul, abs_of_pos hL] at h1
  have h2 : (|n| : ℝ) ≤ |(((a : ℤ) * n : ℤ) : ℝ)| := by
    push_cast
    rw [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast ha)
  have h3 : (|n| : ℝ) ≤ ⌈C / Real.log (ideleNorm (E := E) (eIdele E))⌉₊ :=
    (h2.trans ((le_div_iff₀ hL).2 h1)).trans (Nat.le_ceil _)
  exact_mod_cast h3

end GlobalTheory.CentralExponent
end
end

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_splitCentre_exponent_le_of_conj_mem_compact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ W : Set (GA E a), IsCompact W → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (g : GA E a), g⁻¹ * (ratGL E a γ * GlobalTheory.UnitaryBC.splitCentre E a 1 ^ n) * g ∈ W → |n| ≤ n₀ := by
  atlas_forward_decl GlobalTheory.CentralExponent.abs_le_of_conj_mem
end

section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem card_latticeGL_conj_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ A : ℕ,
    ∀ W : Set (GA E a), IsCompact W → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : GL (Fin a) (Cinf E),
      {γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.Finite ∧
      ({γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.ncard : ℝ) ≤
        C * height y ^ (2 * A) := by
  intro E _ _ _ a
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · refine ⟨0, fun W _ => ⟨1, zero_le_one, fun y => ?_⟩⟩
    have hs : ∀ s : Set (GlobalTheory.UnitaryBC.latticeGL E 0), s.Subsingleton := fun s x _ z _ =>
      Subtype.ext (Units.ext (Matrix.ext fun i => Fin.elim0 i))
    refine ⟨(hs _).finite, ?_⟩
    rw [pow_zero, mul_one]
    exact_mod_cast (Set.ncard_le_one_iff (hs _).finite).2 fun h1 h2 => hs _ h1 h2
  obtain ⟨m, hm⟩ := GlobalTheory.T.rationalGL_boundedSize_compactFinite_polynomialCount E a
  refine ⟨m, fun W hW => ?_⟩
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.abs_splitCentre_exponent_le_of_conj_mem_compact E a ha W hW
  obtain ⟨hInf, hFin, -, -⟩ := GlobalTheory.T.continuous_GL_adelic_projections_inclusions E a
  set e : GA E a := GlobalTheory.UnitaryBC.splitCentre E a 1 with he
  set W' : Set (GA E a) := ⋃ n ∈ Finset.Icc (-(n₀ : ℤ)) n₀, (fun g => g * (e ^ n)⁻¹) '' W with hW'
  have hW'c : IsCompact W' := (Finset.Icc (-(n₀ : ℤ)) n₀).isCompact_biUnion fun n _ =>
    hW.image (continuous_mul_right _)
  set Kf : Set (GL (Fin a) (Af E)) := (fun g : GA E a => Matrix.GeneralLinearGroup.map (pFin E) g) '' W' with hKf
  have hKfc : IsCompact Kf := hW'c.image hFin
  have hv : Continuous fun g : GA E a =>
      ((Matrix.GeneralLinearGroup.map (pInf E) g : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) :=
    Units.continuous_val.comp hInf
  have ht : Continuous (toL : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a) := continuous_id
  have hcn : Continuous fun g : GA E a => ‖toL (Matrix.GeneralLinearGroup.map (pInf E) g).val‖ :=
    continuous_norm.comp (ht.comp hv)
  obtain ⟨B₀, hB₀⟩ := hW'c.exists_bound_of_continuousOn hcn.continuousOn
  set B : ℝ := max 0 B₀ with hB
  have hB0 : 0 ≤ B := le_max_left _ _
  have hBb : ∀ w ∈ W', ‖toL (Matrix.GeneralLinearGroup.map (pInf E) w).val‖ ≤ B := fun w hw =>
    (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB₀ w hw).trans (le_max_right _ _))
  obtain ⟨C₁, hC₁0, hC₁⟩ := hm Kf hKfc
  set N : ℝ := ((Set.Icc (-(n₀ : ℤ)) n₀).ncard : ℝ) with hN
  set c : ℝ := 1 + (a : ℝ) ^ 2 * B with hc
  have hc1 : 1 ≤ c := by
    have : 0 ≤ (a : ℝ) ^ 2 * B := by positivity
    linarith
  refine ⟨C₁ * c ^ m * N, by positivity, fun y => ?_⟩
  set T : ℝ := c * height y ^ 2 with hT
  have hh := one_le_height y
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le hc1 (one_le_pow₀ hh)
  obtain ⟨hfin, hcard⟩ := hC₁ T hT1
  set S := {δ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ)).val‖ ≤ T ∧
    Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) ∈ Kf} with hS
  let f : GL (Fin a) E × ℤ → GlobalTheory.UnitaryBC.latticeGL E a := fun p =>
    ⟨ratGL E a p.1 * e ^ p.2, GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.2 ⟨p.1, p.2, rfl⟩⟩
  have hsub : {γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W} ⊆
      f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀) := by
    rintro ⟨γ, hγ⟩ hγW
    obtain ⟨δ, n, rfl⟩ := GlobalTheory.CuspRep.CuspidalL2GL.mem_latticeGL_iff.1 hγ
    change (infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y ∈ W at hγW
    have hn : |n| ≤ n₀ := hn₀ δ n _ hγW
    have hn' : n ∈ Set.Icc (-(n₀ : ℤ)) n₀ := abs_le.1 hn
    set w := (infGL E a y)⁻¹ * ratGL E a δ * infGL E a y with hw
    have hcomm : Commute (e ^ n) (infGL E a y) :=
      (Commute.zpow_left (GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm 1 (infGL E a y)) n)
    have hwW : w ∈ W' := by
      refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_Icc.2 hn')) ⟨_, hγW, ?_⟩
      change (infGL E a y)⁻¹ * (ratGL E a δ * e ^ n) * infGL E a y * (e ^ n)⁻¹ = w
      simp only [mul_assoc]
      rw [← mul_assoc (e ^ n) (infGL E a y), hcomm.eq, mul_inv_cancel_right]
      all_goals simp only [hw, mul_assoc]
    have hδ : ratGL E a δ = infGL E a y * w * (infGL E a y)⁻¹ := by rw [hw]; group
    refine ⟨(δ, n), ⟨⟨?_, ?_⟩, hn'⟩, rfl⟩
    · have e1 : Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a δ) =
          y * Matrix.GeneralLinearGroup.map (pInf E) w * y⁻¹ := by
        rw [hδ, map_mul, map_mul, map_inv, pInf_infGL]
      rw [e1, Units.val_mul, Units.val_mul]
      have hw' := hBb w hwW
      have p1 := GlobalTheory.AutGrowth.norm_toL_mul_le (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val) (y⁻¹).val
      have p2 := GlobalTheory.AutGrowth.norm_toL_mul_le y.val (Matrix.GeneralLinearGroup.map (pInf E) w).val
      have hy1 : ‖toL y.val‖ ≤ height y := by
        unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
      have hy2 : ‖toL (y⁻¹).val‖ ≤ height y := by
        unfold height; linarith [norm_nonneg (toL y.val)]
      have n1 := norm_nonneg (toL y.val)
      have n2 := norm_nonneg (toL (y⁻¹).val)
      have n3 := norm_nonneg (toL (Matrix.GeneralLinearGroup.map (pInf E) w).val)
      have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have q1 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val)‖ ≤ a * (height y * B) :=
        p2.trans (mul_le_mul_of_nonneg_left (mul_le_mul hy1 hw' n3 (by linarith)) ha0)
      have q2 : ‖toL (y.val * (Matrix.GeneralLinearGroup.map (pInf E) w).val * (y⁻¹).val)‖ ≤
          a * ((a * (height y * B)) * height y) :=
        p1.trans (mul_le_mul_of_nonneg_left (mul_le_mul q1 hy2 n2 (by positivity)) ha0)
      refine q2.trans ?_
      rw [hT, hc]
      have : 0 ≤ height y ^ 2 := by positivity
      nlinarith
    · have e2 : Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a δ) =
          Matrix.GeneralLinearGroup.map (pFin E) w := by
        rw [hδ, map_mul, map_mul, map_inv, pFin_infGL, inv_one, one_mul, mul_one]
      rw [e2]
      exact ⟨w, hwW, rfl⟩
  have hfin2 : (f '' (S ×ˢ Set.Icc (-(n₀ : ℤ)) n₀)).Finite := (hfin.prod (Set.finite_Icc _ _)).image f
  refine ⟨hfin2.subset hsub, ?_⟩
  have k1 := Set.ncard_le_ncard hsub hfin2
  have k2 := Set.ncard_image_le (f := f) (hfin.prod (Set.finite_Icc (-(n₀ : ℤ)) n₀))
  rw [Set.ncard_prod] at k2
  have k3 : (({γ : GlobalTheory.UnitaryBC.latticeGL E a | (infGL E a y)⁻¹ * (γ : GA E a) * infGL E a y ∈ W}.ncard : ℕ) : ℝ) ≤
      (S.ncard : ℝ) * N := by rw [hN]; exact_mod_cast k1.trans k2
  refine k3.trans ?_
  have hN0 : 0 ≤ N := by positivity
  calc (S.ncard : ℝ) * N ≤ C₁ * T ^ m * N := mul_le_mul_of_nonneg_right hcard hN0
    _ = C₁ * c ^ m * N * height y ^ (2 * m) := by rw [hT, mul_pow, ← pow_mul, mul_comm 2 m]; ring

end GlobalTheory
end
