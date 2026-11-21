import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelCompactTranslateBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSemisimpleFlagStabilizer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepConeWeightRatioBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergCoords
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSide
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideFurther

section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_compact_translate_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → ∀ (K : Subgroup (GAd σ J)), IsCompact (K : Set (GAd σ J)) → ∀ c : ℝ, 0 < c → ∀ (C : Set (GAd σ J)), IsCompact C → ∃ t1 : ℝ, ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ K, ∀ γ : GRat σ J, (p * a * k)⁻¹ * ratEmb σ J γ * (p * a * k) ∈ C → ∀ j : Fin r, t1 < t j → (∀ j' : Fin r, j'.val = j.val + 1 → t1 * t j' < t j) → (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, γ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) := by
  first | exact @GlobalTheory.CompanionTheory.FlagKey.flag_key | exact GlobalTheory.CompanionTheory.FlagKey.flag_key | (intros; apply GlobalTheory.CompanionTheory.FlagKey.flag_key <;> assumption)
end

section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_semisimple_flag_stabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (γ : GRat σ J), GlobalTheory.Orb.IsRegSS γ.1.1 → (∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, γ.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0)) → ∃ g : GRat σ J, (∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, g.1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0)) ∧ ∀ j ∈ S, (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, (g⁻¹ * γ * g).1.1 *ᵥ (fun a => X a l) = X *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) ∧ (∀ l : Fin r, l ≤ j → ∃ b : Fin r → E, (g⁻¹ * γ * g).1.1 *ᵥ (fun a => Y a l) = Y *ᵥ b ∧ ∀ m : Fin r, j < m → b m = 0) := by
  first | exact @GlobalTheory.CompanionTheory.LeviConj.conj_into_levi | exact GlobalTheory.CompanionTheory.LeviConj.conj_into_levi | (intros; apply GlobalTheory.CompanionTheory.LeviConj.conj_into_levi <;> assumption)
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_coords {K : Type} [Field K] {n : ℕ} (S : Submodule K (Fin n → K)) (P : Matrix (Fin n) (Fin n) K)
    (hP : ∀ v, P *ᵥ v ∈ S) :
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) K) (C : Matrix (Fin m) (Fin n) K),
      (∀ w, Z *ᵥ w ∈ S) ∧ Z * C = P ∧ Function.Injective Z.mulVec := by
  classical
  let b := Module.finBasis K S
  let Z : Matrix (Fin n) (Fin (Module.finrank K S)) K := Matrix.of fun i k => (b k : Fin n → K) i
  have hZ : ∀ w, Z *ᵥ w = ((∑ k, w k • b k : S) : Fin n → K) := by
    intro w
    ext i
    simp [Z, Matrix.mulVec, dotProduct, mul_comm, Submodule.coe_sum, Finset.sum_apply]
  let L : (Fin n → K) →ₗ[K] S := P.mulVecLin.codRestrict S hP
  let c : (Fin n → K) →ₗ[K] (Fin (Module.finrank K S) → K) := b.equivFun.toLinearMap ∘ₗ L
  refine ⟨_, Z, LinearMap.toMatrix' c, fun w => by rw [hZ]; exact Subtype.property _, ?_, ?_⟩
  · apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, hZ]
    have : (∑ k, c v k • b k : S) = L v := b.sum_equivFun (L v)
    rw [this]
    rfl
  · intro w w' h
    rw [hZ, hZ] at h
    have h' := Subtype.coe_injective h
    rw [← b.equivFun_symm_apply, ← b.equivFun_symm_apply] at h'
    exact b.equivFun.symm.injective h'

theorem exists_witt_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (Qi : Matrix (Idx r m) (Fin n) E), cT (σ : E →+* E) X * J * Z = 0 ∧ cT (σ : E →+* E) Y * J * Z = 0 ∧ Qi * frm X Z Y = 1 ∧ frm X Z Y * Qi = 1 := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW
  have hc : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hcc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := Matrix.ext fun i j => sigma_sigma hσ _
  obtain ⟨A, hA⟩ : ∃ A, A = cT (σ : E →+* E) X * J := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = cT (σ : E →+* E) Y * J := ⟨_, rfl⟩
  have hAX : A * X = 0 := hA ▸ hW.xx
  have hBY : B * Y = 0 := hB ▸ hW.yy
  have hAY : A * Y = 1 := hA ▸ hW.xy
  have hBX : B * X = 1 := by
    have h := congrArg (cT (σ : E →+* E)) hW.xy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hc, hcc, Formalism.UG.cT_one, ← Matrix.mul_assoc] at h
    rw [hB, h]
  obtain ⟨P, hPd⟩ : ∃ P : Matrix (Fin n) (Fin n) E, P = 1 - X * B - Y * A := ⟨_, rfl⟩
  have hAP : A * P = 0 := by
    rw [hPd, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hBP : B * P = 0 := by
    rw [hPd, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX, hBY,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hPX : P * X = 0 := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBX, hAX,
      Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  have hPY : P * Y = 0 := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBY, hAY,
      Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  obtain ⟨m, Z, C, hS, hZC, hinj⟩ := exists_coords
    (LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) P (fun v => by
      refine ⟨?_, ?_⟩
      · simp [Matrix.mulVec_mulVec, hAP]
      · simp [Matrix.mulVec_mulVec, hBP])
  have hAZ : A * Z = 0 := by
    apply Matrix.mulVec_injective
    funext w
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    simpa using (hS w).1
  have hBZ : B * Z = 0 := by
    apply Matrix.mulVec_injective
    funext w
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    simpa using (hS w).2
  have hcan : ∀ {ι : Type} (M M' : Matrix (Fin m) ι E), Z * M = Z * M' → M = M' := by
    intro ι M M' h
    ext i j
    exact congrFun (hinj (a₁ := fun i => M i j) (a₂ := fun i => M' i j)
      (funext fun a => congrFun (congrFun h a) j)) i
  have hPZ : P * Z = Z := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBZ, hAZ,
      Matrix.mul_zero, Matrix.mul_zero, sub_zero, sub_zero]
  have hCZ : C * Z = 1 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPZ, Matrix.mul_one])
  have hCX : C * X = 0 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPX, Matrix.mul_zero])
  have hCY : C * Y = 0 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPY, Matrix.mul_zero])
  refine ⟨m, Z, Matrix.fromRows B (Matrix.fromRows C A), hA ▸ hAZ, hB ▸ hBZ, ?_, ?_⟩
  · rw [frm, Matrix.fromRows_mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      hBX, hBZ, hBY, hCX, hAX, hCZ, hCY, hAZ, hAY]
    ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply]
  · rw [frm, Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows, hZC, hPd]
    abel

end GlobalTheory.CompanionTheory.CFin

end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_witt_complement_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (Qi : Matrix (Idx r m) (Fin n) E), cT (σ : E →+* E) X * J * Z = 0 ∧ cT (σ : E →+* E) Y * J * Z = 0 ∧ Qi * frm X Z Y = 1 ∧ frm X Z Y * Qi = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.exists_witt_basis
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin.Tri

theorem cnt_le {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : cnt S i ≤ S.card := by
  unfold cnt
  exact_mod_cast Finset.card_filter_le _ _

theorem exists_least {r : ℕ} {S : Finset (Fin r)} {i : Fin r} (h : cnt S i < S.card) :
    ∃ j ∈ S, i ≤ j ∧ ∀ j' ∈ S, i ≤ j' → j ≤ j' := by
  have hne : (S.filter (i ≤ ·)).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hn
    have : S.filter (· < i) = S := Finset.filter_true_of_mem fun x hx => not_le.mp (hn hx)
    simp [cnt, this] at h
  refine ⟨(S.filter (i ≤ ·)).min' hne, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  · intro j' hj' hij'
    exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj', hij'⟩)

theorem exists_between {r : ℕ} {S : Finset (Fin r)} {i k : Fin r} (h : cnt S i < cnt S k) :
    ∃ t ∈ S, i ≤ t ∧ t < k := by
  by_contra hn
  push_neg at hn
  have hsub : S.filter (· < k) ⊆ S.filter (· < i) := by
    intro t ht
    obtain ⟨htS, htk⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨htS, ?_⟩
    by_contra hti
    exact absurd htk (not_lt.mpr (hn t htS (not_lt.mp hti)))
  have := Finset.card_le_card hsub
  unfold cnt at h
  omega

theorem inv_neg_tri {ι : Type} [Fintype ι] [DecidableEq ι] {L : Type} [Field L] (lv : ι → ℤ)
    {M M' : Matrix ι ι L} (h : M * M' = 1)
    (hM : ∀ u v, lv v < lv u → lv v < 0 → M u v = 0) :
    ∀ u v, lv v < lv u → lv v < 0 → M' u v = 0 := by
  intro u v huv hv
  letI : Invertible M := ⟨M', mul_eq_one_comm.mp h, h⟩
  have hinv : M⁻¹ = M' := Matrix.inv_eq_right_inv h
  have hb : M.BlockTriangular (fun w => if lv w ≤ lv v then (0 : ℤ) else 1) := by
    intro a b hab
    by_cases hb' : lv b ≤ lv v
    · by_cases ha' : lv a ≤ lv v
      · simp [hb', ha'] at hab
      · exact hM a b (by omega) (by omega)
    · by_cases ha' : lv a ≤ lv v <;> simp [hb', ha'] at hab
  have := Matrix.blockTriangular_inv_of_blockTriangular hb
  rw [hinv] at this
  apply this
  have h1 : ¬ lv u ≤ lv v := by omega
  simp [h1]

theorem col_zero {L : Type} [Field L] {n r m : ℕ} (X Y : Matrix (Fin n) (Fin r) L)
    (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L)
    (hQ : Qi * frm X Z Y = 1) (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L)
    (hst : ∀ j ∈ S, StabUpTo X g j) (u v : Idx r m)
    (huv : lev m S v < lev m S u) (hv : lev m S v < 0) : (Qi * g * frm X Z Y) u v = 0 := by
  rcases v with i | k | i
  · have hi : cnt S i < S.card := by simpa [lev] using hv
    obtain ⟨j, hjS, hij, hmin⟩ := exists_least hi
    obtain ⟨b, hb, hbz⟩ := hst j hjS i hij
    have hc : X *ᵥ b = frm X Z Y *ᵥ (Sum.elim b (fun _ => 0)) := by
      ext a
      simp [frm, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    have hcol : (fun w => (Qi * g * frm X Z Y) w (Sum.inl i)) = Sum.elim b (fun _ => 0) := by
      have e1 : (fun w => (Qi * g * frm X Z Y) w (Sum.inl i))
          = Qi *ᵥ (g *ᵥ (fun a => X a i)) := by
        ext w
        rw [Matrix.mul_assoc]
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, frm]
      rw [e1, hb, hc, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
    have hval : (Qi * g * frm X Z Y) u (Sum.inl i) = Sum.elim b (fun _ => 0) u := congrFun hcol u
    rw [hval]
    rcases u with k | w
    · simp only [Sum.elim_inl]
      have hc' : cnt S i < cnt S k := by simpa [lev] using huv
      obtain ⟨t, htS, hit, htk⟩ := exists_between hc'
      exact hbz k (lt_of_le_of_lt (hmin t htS hit) htk)
    · simp
  · simp [lev] at hv
  · have := cnt_le S i
    simp only [lev] at hv
    omega

theorem cT_mul' {L : Type} [Field L] (s : L →+* L) {a b c : Type} [Fintype b]
    (A : Matrix a b L) (B : Matrix b c L) : cT s (A * B) = cT s B * cT s A := by
  simp [cT, Matrix.transpose_mul, Matrix.map_mul]

theorem cT_one' {L : Type} [Field L] (s : L →+* L) {a : Type} [DecidableEq a] :
    cT s (1 : Matrix a a L) = 1 := by
  simp [cT]

theorem block_tri (L : Type) [Field L] (s : L →+* L) (n r m : ℕ)
    (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L)
    (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L)
    (hXX : cT s X * J * X = 0) (hXY : cT s X * J * Y = 1) (hXZ : cT s X * J * Z = 0)
    (hQ : Qi * frm X Z Y = 1) (hQ' : frm X Z Y * Qi = 1) (S : Finset (Fin r))
    (g : Matrix (Fin n) (Fin n) L) (hg : IsUnit g) (hJ : cT s g * J * g = J)
    (hst : ∀ j ∈ S, StabUpTo X g j) :
    (Qi * g * frm X Z Y).BlockTriangular (lev m S) := by
  obtain ⟨gi, h1⟩ := hg.exists_right_inv
  have hrow0 : cT s X * J * frm X Z Y = Matrix.fromCols (0 : Matrix (Fin r) (Fin r) L)
        (Matrix.fromCols (0 : Matrix (Fin r) (Fin m) L) (1 : Matrix (Fin r) (Fin r) L)) := by
    rw [frm, Matrix.mul_fromCols, Matrix.mul_fromCols, hXX, hXZ, hXY]
  set Q := frm X Z Y with hQdef
  set M := Qi * g * Q with hMdef
  set M' := Qi * gi * Q with hM'def
  have hMM' : M * M' = 1 := by
    calc M * M' = Qi * g * (Q * Qi) * gi * Q := by simp only [hMdef, hM'def, Matrix.mul_assoc]
      _ = Qi * (g * gi) * Q := by rw [hQ']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hQ]
  have A1 : ∀ u v, lev m S v < lev m S u → lev m S v < 0 → M u v = 0 :=
    fun u v huv hv => col_zero X Y Z Qi hQ S g hst u v huv hv
  have A2 := inv_neg_tri (lev m S) hMM' A1
  set H := cT s Q * J * Q with hHdef
  have hgJ : cT s gi * J = J * g := by
    have e : cT s gi * cT s g = 1 := by
      rw [← cT_mul', h1, cT_one']
    calc cT s gi * J = cT s gi * (cT s g * J * g) := by rw [hJ]
      _ = (cT s gi * cT s g) * J * g := by simp only [Matrix.mul_assoc]
      _ = J * g := by rw [e, Matrix.one_mul]
  have hHM : H * M = cT s M' * H := by
    have e : cT s Qi * cT s Q = 1 := by rw [← cT_mul', hQ', cT_one']
    calc H * M = cT s Q * J * (Q * Qi) * g * Q := by simp only [hHdef, hMdef, Matrix.mul_assoc]
      _ = cT s Q * (J * g) * Q := by rw [hQ']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = cT s Q * (cT s gi * J) * Q := by rw [hgJ]
      _ = cT s Q * cT s gi * (cT s Qi * cT s Q) * J * Q := by rw [e]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = cT s M' * H := by simp only [hM'def, hHdef, cT_mul', Matrix.mul_assoc]
  have hrow : ∀ l w, H (Sum.inl l) w = (Matrix.fromCols (0 : Matrix (Fin r) (Fin r) L)
      (Matrix.fromCols (0 : Matrix (Fin r) (Fin m) L) (1 : Matrix (Fin r) (Fin r) L))) l w := by
    intro l w
    rw [← hrow0]
    simp only [hHdef, hQdef, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, frm,
      Matrix.fromCols_apply_inl]
  have lx : ∀ i, lev m S (Sum.inl i) = cnt S i - S.card := fun _ => rfl
  have lz : ∀ k, lev m S (Sum.inr (Sum.inl k)) = 0 := fun _ => rfl
  have ly : ∀ i, lev m S (Sum.inr (Sum.inr i)) = S.card - cnt S i := fun _ => rfl
  intro u v huv
  by_cases hv : lev m S v < 0
  · exact A1 u v huv hv
  push_neg at hv
  rcases u with i | k | l
  · have := cnt_le S i
    rw [lx] at huv
    omega
  · rw [lz] at huv
    omega
  have hl0 : lev m S (Sum.inl l) < 0 := by
    have := cnt_le S l
    rw [ly] at huv; rw [lx]; omega
  have hlv : lev m S v < - lev m S (Sum.inl l) := by rw [ly] at huv; rw [lx]; omega
  have e1 : M (Sum.inr (Sum.inr l)) v = (H * M) (Sum.inl l) v := by
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hrow, Matrix.one_apply]
  rw [e1, hHM, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases hw : lev m S (Sum.inl l) < lev m S w
  · have : M' w (Sum.inl l) = 0 := A2 w _ hw hl0
    simp [cT, this]
  push_neg at hw
  rcases w with l' | k | l'
  · rcases v with a | b | c
    · simp [hrow]
    · simp [hrow]
    · by_cases hc : l' = c
      · subst hc
        have := cnt_le S l'
        simp only [lx, ly] at hw hlv
        omega
      · simp [hrow, Matrix.one_apply, hc]
  · rw [lz] at hw
    omega
  · have := cnt_le S l'
    rw [ly] at hw
    omega

theorem witt_blockTriangular : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (∀ j ∈ S, StabUpTo X g j) → (Qi * g * frm X Z Y).BlockTriangular (lev m S) := by
  intro L _ s _ n r m J X Y Z Qi _ hXX _ hXY hXZ _ hQ hQ' S g hg hJ hst
  exact block_tri L s n r m J X Y Z Qi hXX hXY hXZ hQ hQ' S g hg hJ hst

end GlobalTheory.CompanionTheory.CFin.Tri
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_stabilizer_flag_criterion : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (∀ j ∈ S, StabUpTo X g j) → (Qi * g * frm X Z Y).BlockTriangular (lev m S) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.Tri.witt_blockTriangular
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin.BdU

theorem gram_apply {L : Type} [CommRing L] (s : L →+* L) {a b c : Type} [Fintype a]
    (M : Matrix a b L) (H : Matrix a a L) (N : Matrix a c L) (i : b) (j : c) :
    (cT s M * H * N) i j = ∑ k, ∑ l, s (M k i) * H k l * N l j := by
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem cT_cT_self {L : Type} [CommRing L] (s : L →+* L) (hs : ∀ x, s (s x) = x) {a b : Type}
    (M : Matrix a b L) : cT s (cT s M) = M := by
  ext i j
  simp [cT, hs]

theorem gram_bd {ι L : Type} [Fintype ι] [CommRing L] (s : L →+* L) (b : ι → ℤ)
    (G H : Matrix ι ι L) (hG : G.BlockTriangular b) (hH : ∀ u v, H u v ≠ 0 → b u + b v = 0)
    (hGH : cT s G * H * G = H) : cT s (bd b G) * H * bd b G = H := by
  ext i j
  have e := congrFun (congrFun hGH i) j
  rw [gram_apply] at e ⊢
  by_cases hij : b i + b j = 0
  · rw [← e]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    simp only [bd, Matrix.of_apply]
    by_cases hGki : G k i = 0
    · simp [hGki]
    by_cases hGlj : G l j = 0
    · simp [hGlj]
    by_cases hHkl : H k l = 0
    · simp [hHkl]
    have h1 := hH k l hHkl
    have h2 : ¬ b i < b k := fun hlt => hGki (hG hlt)
    have h3 : ¬ b j < b l := fun hlt => hGlj (hG hlt)
    have hk : b k = b i := by omega
    have hl : b l = b j := by omega
    simp [hk, hl]
  · have hHij : H i j = 0 := by
      by_contra hne
      exact hij (hH i j hne)
    rw [hHij]
    refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))
    simp only [bd, Matrix.of_apply]
    by_cases hk : b k = b i
    · by_cases hl : b l = b j
      · have hHkl : H k l = 0 := by
          by_contra hne
          have := hH k l hne
          exact hij (by omega)
        simp [hHkl]
      · simp [hl]
    · simp [hk]

theorem levi_unitary {ι L : Type} [Fintype ι] [DecidableEq ι] [Field L] (s : L →+* L) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) L) (Q : Matrix (Fin n) ι L) (Qi : Matrix ι (Fin n) L) (b : ι → ℤ)
    (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hH : ∀ u v, (cT s Q * J * Q) u v ≠ 0 → b u + b v = 0)
    (g : Matrix (Fin n) (Fin n) L) (hg : IsUnit g) (hgJ : cT s g * J * g = J)
    (hB : (Qi * g * Q).BlockTriangular b) :
    IsUnit (Q * bd b (Qi * g * Q) * Qi) ∧
      cT s (Q * bd b (Qi * g * Q) * Qi) * J * (Q * bd b (Qi * g * Q) * Qi) = J := by
  have cTm : ∀ {a b c : Type} [Fintype b] (A : Matrix a b L) (B : Matrix b c L),
      cT s (A * B) = cT s B * cT s A := by
    intro a b c _ A B
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have cT1 : cT s (1 : Matrix (Fin n) (Fin n) L) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]
  have hQQ : cT s Qi * cT s Q = 1 := by rw [← cTm, h2, cT1]
  have hGu : cT s (Qi * g * Q) * (cT s Q * J * Q) * (Qi * g * Q) = cT s Q * J * Q := by
    calc cT s (Qi * g * Q) * (cT s Q * J * Q) * (Qi * g * Q)
        = cT s Q * (cT s g * ((cT s Qi * cT s Q) * (J * ((Q * Qi) * (g * Q))))) := by
          rw [cTm, cTm]
          simp only [Matrix.mul_assoc]
      _ = cT s Q * ((cT s g * J * g) * Q) := by
          rw [hQQ, h2, Matrix.one_mul, Matrix.one_mul]
          simp only [Matrix.mul_assoc]
      _ = cT s Q * J * Q := by rw [hgJ, Matrix.mul_assoc]
  have hbdu := gram_bd s b (Qi * g * Q) (cT s Q * J * Q) hB hH hGu
  obtain ⟨u, hu⟩ := hg
  have hGunit : IsUnit (Qi * g * Q) := by
    refine ⟨⟨Qi * g * Q, Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q, ?_, ?_⟩, rfl⟩
    · calc Qi * g * Q * (Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q) = Qi * (g * (Q * Qi) * (↑u⁻¹ : Matrix (Fin n) (Fin n) L)) * Q := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, ← hu, Units.mul_inv, Matrix.mul_one, h1]
    · calc Qi * (↑u⁻¹ : Matrix (Fin n) (Fin n) L) * Q * (Qi * g * Q) = Qi * ((↑u⁻¹ : Matrix (Fin n) (Fin n) L) * (Q * Qi) * g) * Q := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, ← hu, Units.inv_mul, Matrix.mul_one, h1]
  have hbdtri : (bd b (Qi * g * Q)).BlockTriangular b := by
    intro i j hij
    simp only [bd, Matrix.of_apply]
    rw [if_neg (ne_of_gt hij)]
  have hdet : (bd b (Qi * g * Q)).det = (Qi * g * Q).det := by
    rw [hbdtri.det, hB.det]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    congr 1
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply, bd]
    rw [if_pos (i.2.trans j.2.symm)]
  have hbdunit : IsUnit (bd b (Qi * g * Q)) := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet, ← Matrix.isUnit_iff_isUnit_det]
    exact hGunit
  obtain ⟨w, hw⟩ := hbdunit
  refine ⟨⟨⟨Q * (↑w : Matrix ι ι L) * Qi, Q * (↑w⁻¹ : Matrix ι ι L) * Qi, ?_, ?_⟩, ?_⟩, ?_⟩
  · calc Q * (↑w : Matrix ι ι L) * Qi * (Q * (↑w⁻¹ : Matrix ι ι L) * Qi) = Q * ((↑w : Matrix ι ι L) * (Qi * Q) * (↑w⁻¹ : Matrix ι ι L)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Units.mul_inv, Matrix.mul_one, h2]
  · calc Q * (↑w⁻¹ : Matrix ι ι L) * Qi * (Q * (↑w : Matrix ι ι L) * Qi) = Q * ((↑w⁻¹ : Matrix ι ι L) * (Qi * Q) * (↑w : Matrix ι ι L)) * Qi := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, Units.inv_mul, Matrix.mul_one, h2]
  · show Q * (↑w : Matrix ι ι L) * Qi = Q * bd b (Qi * g * Q) * Qi
    rw [hw]
  · calc cT s (Q * bd b (Qi * g * Q) * Qi) * J * (Q * bd b (Qi * g * Q) * Qi)
        = cT s Qi * ((cT s (bd b (Qi * g * Q)) * (cT s Q * J * Q) * bd b (Qi * g * Q)) * Qi) := by
          rw [cTm, cTm]
          simp only [Matrix.mul_assoc]
      _ = cT s Qi * ((cT s Q * J * Q) * Qi) := by rw [hbdu]
      _ = (cT s Qi * cT s Q) * J * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hQQ, h2, Matrix.one_mul, Matrix.mul_one]

theorem gram_frm_degree {L : Type} [Field L] (s : L →+* L) (hs : ∀ x, s (s x) = x) {n r m : ℕ}
    (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L)
    (hJ : cT s J = J) (hXX : cT s X * J * X = 0) (hYY : cT s Y * J * Y = 0)
    (hXY : cT s X * J * Y = 1) (hXZ : cT s X * J * Z = 0) (hYZ : cT s Y * J * Z = 0)
    (S : Finset (Fin r)) (u v : Idx r m)
    (h : (cT s (frm X Z Y) * J * frm X Z Y) u v ≠ 0) : lev m S u + lev m S v = 0 := by
  have cTm : ∀ {a b c : Type} [Fintype b] (A : Matrix a b L) (B : Matrix b c L),
      cT s (A * B) = cT s B * cT s A := by
    intro a b c _ A B
    unfold Formalism.UG.cT
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have cT1 : cT s (1 : Matrix (Fin r) (Fin r) L) = 1 := by
    unfold Formalism.UG.cT
    rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]
  have cT0 : ∀ {a b : Type}, cT s (0 : Matrix a b L) = 0 := by
    intro a b
    unfold Formalism.UG.cT
    ext i j
    simp
  have hYX : cT s Y * J * X = 1 := by
    have e := congrArg (cT s) hXY
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT1, ← Matrix.mul_assoc] at e
    exact e
  have hZX : cT s Z * J * X = 0 := by
    have e := congrArg (cT s) hXZ
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT0, ← Matrix.mul_assoc] at e
    exact e
  have hZY : cT s Z * J * Y = 0 := by
    have e := congrArg (cT s) hYZ
    rw [cTm, cTm, cT_cT_self s hs, hJ, cT0, ← Matrix.mul_assoc] at e
    exact e
  rcases u with i | i | i <;> rcases v with j | j | j
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inl j) = (cT s X * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXX] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inr (Sum.inl j)) = (cT s X * J * Z) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXZ] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inl i) (Sum.inr (Sum.inr j)) = (cT s X * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hXY] at h
    have hij : i = j := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hij
    show (cnt S i - (S.card : ℤ)) + ((S.card : ℤ) - cnt S i) = 0
    ring
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inl i)) (Sum.inl j) = (cT s Z * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hZX] at h
    simp at h
  · show (0 : ℤ) + 0 = 0
    rfl
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j)) = (cT s Z * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hZY] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inl j) = (cT s Y * J * X) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYX] at h
    have hij : i = j := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hij
    show ((S.card : ℤ) - cnt S i) + (cnt S i - (S.card : ℤ)) = 0
    ring
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) = (cT s Y * J * Z) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYZ] at h
    simp at h
  · have e : (cT s (frm X Z Y) * J * frm X Z Y) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) = (cT s Y * J * Y) i j := by
      rw [gram_apply, gram_apply]
      rfl
    rw [e, hYY] at h
    simp at h

theorem bd_unitary : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (Qi * g * frm X Z Y).BlockTriangular (lev m S) → IsUnit (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) ∧ cT s (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) * J * (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) = J := by
  intro L _ s hs n r m J X Y Z Qi hJ hXX hYY hXY hXZ hYZ h1 h2 S g hg hgJ hB
  exact levi_unitary s J (frm X Z Y) Qi (lev m S) h1 h2
    (fun u v h => gram_frm_degree s hs J X Y Z hJ hXX hYY hXY hXZ hYZ S u v h) g hg hgJ hB

end GlobalTheory.CompanionTheory.CFin.BdU

end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_stabilizer_flag_converse : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (Qi * g * frm X Z Y).BlockTriangular (lev m S) → IsUnit (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) ∧ cT s (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) * J * (frm X Z Y * bd (lev m S) (Qi * g * frm X Z Y) * Qi) = J := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.BdU.bd_unitary
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem archMat_entries_bounded_of_isCompact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (GAd σ J))
    (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ C, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
      ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ B := by
  classical
  have hb : ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
      ∃ b : ℝ, ∀ g ∈ C, ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ b := by
    intro w τ i j
    have hc : Continuous fun g : GAd σ J => ‖archMat σ J τ (projArch σ J w g) i j‖ :=
      (((GlobalTheory.Orb.continuous_archMat σ J τ).comp (continuous_projArch σ J w)).matrix_elem i j).norm
    obtain ⟨b, hb⟩ := hC.bddAbove_image hc.continuousOn
    exact ⟨b, fun g hg => hb ⟨g, hg, rfl⟩⟩
  choose b hb using hb
  haveI : Fintype (InfinitePlace F) := inferInstance
  refine ⟨∑ w : InfinitePlace F, ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j|,
    Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _, fun g hg w τ i j => ?_⟩
  calc ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ b w τ i j := hb w τ i j g hg
    _ ≤ |b w τ i j| := le_abs_self _
    _ ≤ ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun j => |b w τ i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun i => ∑ j : Fin n, |b w τ i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun τ => ∑ i : Fin n, ∑ j : Fin n, |b w τ i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ τ)
    _ ≤ ∑ w : InfinitePlace F, ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j| :=
        Finset.single_le_sum (f := fun w => ∑ τ : EmbOver E w, ∑ i : Fin n, ∑ j : Fin n, |b w τ i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (Finset.mem_univ w)

end GlobalTheory.CompanionTheory.CFin
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_archimedean_entries_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (C : Set (GAd σ J)), IsCompact C → ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ C, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n), ‖archMat σ J τ (projArch σ J w g) i j‖ ≤ B := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.archMat_entries_bounded_of_isCompact
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem torus_diag_witt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n r m : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (Z : Matrix (Fin n) (Fin m) E), cT (σ : E →+* E) X * J * Z = 0 → cT (σ : E →+* E) Y * J * Z = 0 → ∀ (t : Fin r → ℝ) (a : GAd σ J), IsTorusElt σ J X Y t a → ∀ (w : InfinitePlace F) (τ : EmbOver E w), archMat σ J τ (projArch σ J w a) * (frm X Z Y).map τ.1 = (frm X Z Y).map τ.1 * diagonal (fun u => ((wt m t u : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ σ n r m J X Y Z hXZ hYZ t a ha w τ
  obtain ⟨hX, hY, hZ⟩ := ha.2 w τ
  have hZc : archMat σ J τ (projArch σ J w a) * Z.map τ.1 = Z.map τ.1 := Matrix.ext fun i j => by
    have h := congrFun (hZ (fun l => Z l j)
      (funext fun i => by simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun hXZ i) j)
      (funext fun i => by simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun hYZ i) j)) i
    simpa [Matrix.mul_apply, mulVec, dotProduct] using h
  have e : (frm X Z Y).map τ.1 = Matrix.fromCols (X.map τ.1) (Matrix.fromCols (Z.map τ.1) (Y.map τ.1)) := by
    ext i (k | k | k) <;> rfl
  rw [e, Matrix.mul_fromCols, Matrix.mul_fromCols, hX, hY, hZc]
  ext i (k | k | k)
  · simp [Matrix.mul_diagonal, wt]
  · simp [Matrix.mul_diagonal, wt]
  · simp [Matrix.mul_diagonal, wt]

end GlobalTheory.CompanionTheory.CFin

end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_archimedean_frame_conjugation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n r m : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (Z : Matrix (Fin n) (Fin m) E), cT (σ : E →+* E) X * J * Z = 0 → cT (σ : E →+* E) Y * J * Z = 0 → ∀ (t : Fin r → ℝ) (a : GAd σ J), IsTorusElt σ J X Y t a → ∀ (w : InfinitePlace F) (τ : EmbOver E w), archMat σ J τ (projArch σ J w a) * (frm X Z Y).map τ.1 = (frm X Z Y).map τ.1 * diagonal (fun u => ((wt m t u : ℝ) : ℂ)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.torus_diag_witt
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem stabUpTo_archMat_of_mem_minParOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) (p : GAd σ J), p ∈ minParOne σ J X → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (j : Fin r), StabUpTo (X.map τ.1) (archMat σ J τ (projArch σ J w p)) j := by
  intro F E _ _ _ _ _ σ h n r J X p hp w τ j
  have := h.1
  obtain ⟨B, hB, hE, -⟩ := hp
  let φ := (infEmb τ).comp (compInf F E w)
  have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
    change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
    simp
  have h2 : (adMat F X).map φ = X.map τ.1 := Matrix.ext fun i j => h0 _
  have h3 : archMat σ J τ (projArch σ J w p) = (matHom _ σ J p).1.map φ := rfl
  have key : archMat σ J τ (projArch σ J w p) * X.map τ.1 = X.map τ.1 * B.map φ := by
    rw [h3, ← h2, ← Matrix.map_mul, hE, Matrix.map_mul]
  intro l hl
  refine ⟨fun m => φ (B m l), ?_, fun m hm => ?_⟩
  · funext a
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply] using congrFun (congrFun key a) l
  · have e : B m l = 0 := hB (show id l < id m from lt_of_le_of_lt hl hm)
    change φ (B m l) = 0
    rw [e, map_zero]

end GlobalTheory.CompanionTheory.CFin

end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_archimedean_stabilizes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) (p : GAd σ J), p ∈ minParOne σ J X → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (j : Fin r), StabUpTo (X.map τ.1) (archMat σ J τ (projArch σ J w p)) j := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.stabUpTo_archMat_of_mem_minParOne
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem archMat_projArch_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J) (w : InfinitePlace F) (τ : EmbOver E w), cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) * J.map τ.1 * archMat σ J τ (projArch σ J w g) = J.map τ.1 := by
  intro F E _ _ _ _ _ σ hcm n J g w τ
  have h := GlobalTheory.HeisCoords.archMat_unitary hcm τ (projArch σ J w g)
  have e : cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) = (archMat σ J τ (projArch σ J w g))ᴴ := by
    ext i j
    simp [cT, Matrix.conjTranspose_apply]
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CFin
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_matrix_preserves_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J) (w : InfinitePlace F) (τ : EmbOver E w), cT (starRingEnd ℂ) (archMat σ J τ (projArch σ J w g)) * J.map τ.1 * archMat σ J τ (projArch σ J w g) = J.map τ.1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.archMat_projArch_unitary
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem archMat_projArch_ratEmb (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : GRat σ J) (w : InfinitePlace F) (τ : EmbOver E w) :
    archMat σ J τ (projArch σ J w (ratEmb σ J γ)) = γ.1.1.map τ.1 := by
  rw [GlobalTheory.Orb.archMat_apply, projArch_ratEmb]
  ext i j
  change infEmb τ ((1 : w.Completion) ⊗ₜ[F] (γ.1.1 i j)) = τ.1 (γ.1.1 i j)
  rw [infEmb_tmul, map_one, one_mul]

end GlobalTheory.CompanionTheory.CFin
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_rational_embedding_map : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : GRat σ J) (w : InfinitePlace F) (τ : EmbOver E w), archMat σ J τ (projArch σ J w (ratEmb σ J γ)) = γ.1.1.map τ.1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.archMat_projArch_ratEmb
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (x : E) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * x) :=
  _root_.UpperTheory.Reformulated.B.DYha3.main x

theorem exists_nat_mul_isIntegral_of_isCompact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {𝒦 : Set (Af F ⊗[F] E)} (h𝒦 : IsCompact 𝒦) :
    ∃ d : ℕ, 0 < d ∧ ∀ e : E, inclR (F := F) (Af F) e ∈ 𝒦 → IsIntegral ℤ ((d : E) * e) := by
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let bb := Algebra.TensorProduct.basis (Af F) b
  have hc : ∀ i, Continuous (fun x : Af F ⊗[F] E => bb.coord i x) := fun i =>
    IsModuleTopology.continuous_of_linearMap (bb.coord i)
  have hcoord : ∀ (e : E) i, bb.coord i (inclR (F := F) (Af F) e) = algebraMap F (Af F) (b.repr e i) := by
    intro e i
    change bb.repr ((1 : Af F) ⊗ₜ[F] e) i = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp [Algebra.algebraMap_eq_smul_one]
  choose m hm hmi using fun i =>
    GroundTheory.Automorphic.CuspidalSpectrum.exists_natCast_mul_integral_of_isCompact F (h𝒦.image (hc i))
  choose D hD hDi using fun i => exists_nat_mul_isIntegral (b i)
  refine ⟨(∏ i, m i) * ∏ i, D i, Nat.mul_pos (Finset.prod_pos fun i _ => hm i)
    (Finset.prod_pos fun i _ => hD i), fun e he => ?_⟩
  have hsum : ((((∏ i, m i) * ∏ i, D i : ℕ)) : E) * e =
      ∑ i, algebraMap F E (((∏ i, m i : ℕ) : F) * b.repr e i) * (((∏ i, D i : ℕ)) : E) * b i := by
    conv_lhs => rw [← b.sum_repr e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [hsum]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  obtain ⟨z, hz⟩ := hmi i (b.repr e i) ⟨_, he, hcoord e i⟩
  have h1 : IsIntegral ℤ (algebraMap F E (((∏ i, m i : ℕ) : F) * b.repr e i)) := by
    have : ((∏ i, m i : ℕ) : F) * b.repr e i = (q : F) * (z : F) := by
      rw [hq, hz, Nat.cast_mul]
      ring
    rw [this]
    exact IsIntegral.algebraMap ((isIntegral_natCast q).mul z.2)
  have h2 : (((∏ i, D i : ℕ)) : E) * b i = (r : E) * ((D i : E) * b i) := by
    rw [hr, Nat.cast_mul]
    ring
  rw [mul_assoc, h2]
  exact h1.mul ((isIntegral_natCast r).mul (hDi i))

end GlobalTheory.CompanionTheory.CFin

namespace GlobalTheory.CompanionTheory.CFin

theorem bounded_denominators : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (𝒞 : Set (GFin σ J)), IsCompact 𝒞 → ∀ {ι : Type} [Fintype ι] (A : Matrix ι (Fin n) E) (B : Matrix (Fin n) ι E), ∃ d : ℕ, 0 < d ∧ ∀ δ : GRat σ J, projFin σ J (ratEmb σ J δ) ∈ 𝒞 → ∀ u v, IsIntegral ℤ ((d : E) * (A * δ.1.1 * B) u v) := by
  intro F E _ _ _ _ _ σ n J 𝒞 h𝒞 ι _ A B
  classical
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  let f : ι → ι → GFin σ J → Af F ⊗[F] E := fun u v y =>
    (A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J y).1 * B.map (inclR (F := F) (Af F))) u v
  have hmat : Continuous fun y : GFin σ J => ((matHom (Af F) σ J y).1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    Units.continuous_val.comp (GlobalTheory.AdelicU.isEmbedding_matHom (Af F) σ J).continuous
  have hf : ∀ u v, Continuous (f u v) := fun u v => by
    have : Continuous fun y : GFin σ J =>
        A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J y).1 * B.map (inclR (F := F) (Af F)) :=
      (continuous_const.matrix_mul hmat).matrix_mul continuous_const
    exact this.matrix_elem u v
  obtain ⟨d, hd, h⟩ := exists_nat_mul_isIntegral_of_isCompact F E
    (𝒦 := ⋃ u, ⋃ v, f u v '' 𝒞)
    (isCompact_iUnion fun u => isCompact_iUnion fun v => h𝒞.image (hf u v))
  refine ⟨d, hd, fun δ hδ u v => h _ ?_⟩
  refine Set.mem_iUnion.2 ⟨u, Set.mem_iUnion.2 ⟨v, _, hδ, ?_⟩⟩
  have hval : ((matHom (Af F) σ J (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J δ))).1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) =
      δ.1.1.map (inclR (F := F) (Af F)) := by
    refine Matrix.ext fun r s => ?_
    change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] (δ.1.1 r s)) =
      (1 : Af F) ⊗ₜ[F] (δ.1.1 r s)
    simp
  change (A.map (inclR (F := F) (Af F)) * (matHom (Af F) σ J (GlobalTheory.AdelicU.projFin σ J (ratEmb σ J δ))).1 *
    B.map (inclR (F := F) (Af F))) u v = _
  rw [hval, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]

end GlobalTheory.CompanionTheory.CFin

end
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_finite_rational_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (𝒞 : Set (GFin σ J)), IsCompact 𝒞 → ∀ {ι : Type} [Fintype ι] (A : Matrix ι (Fin n) E) (B : Matrix (Fin n) ι E), ∃ d : ℕ, 0 < d ∧ ∀ δ : GRat σ J, projFin σ J (ratEmb σ J δ) ∈ 𝒞 → ∀ u v, IsIntegral ℤ ((d : E) * (A * δ.1.1 * B) u v) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.bounded_denominators
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem matrices_bounded_denominator_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsTotallyReal F → ∀ {ι : Type} [Finite ι] (d : ℕ) (B : ℝ), 0 < d → {N : Matrix ι ι E | (∀ u v, IsIntegral ℤ ((d : E) * N u v)) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : ι), ‖τ.1 (N u v)‖ ≤ B}.Finite := by
  intro F E _ _ _ _ _ hF ι _ d B hd
  haveI := hF
  have hS : {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ) * B}.Finite :=
    Embeddings.finite_of_norm_le E ℂ _
  have hd0 : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hT := hS.preimage (f := fun e : E => (d : E) * e)
    (fun a _ b _ h => mul_left_cancel₀ hd0 h)
  have hM := Set.Finite.pi' (fun _ : ι => Set.Finite.pi' (fun _ : ι => hT))
  refine hM.subset ?_
  rintro N ⟨h1, h2⟩ u v
  refine ⟨h1 u v, fun φ => ?_⟩
  have hr : ComplexEmbedding.IsReal (φ.comp (algebraMap F E)) :=
    IsTotallyReal.complexEmbedding_isReal _
  have hb := h2 (InfinitePlace.mk (φ.comp (algebraMap F E)))
    ⟨φ, (InfinitePlace.embedding_mk_eq_of_isReal hr).symm⟩ u v
  rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg d)

end GlobalTheory.CompanionTheory.CFin
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_integral_matrices_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsTotallyReal F → ∀ {ι : Type} [Finite ι] (d : ℕ) (B : ℝ), 0 < d → {N : Matrix ι ι E | (∀ u v, IsIntegral ℤ ((d : E) * N u v)) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : ι), ‖τ.1 (N u v)‖ ≤ B}.Finite := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_ratEmb_eq_of_mem_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J), g ∈ ratPts σ J → ∃ η : GRat σ J, g = ratEmb σ J η := by
  intro F E _ _ _ _ _ σ n J g hg
  rw [← range_ratEmb σ J] at hg
  obtain ⟨η, rfl⟩ := hg
  exact ⟨η, rfl⟩

end GlobalTheory.CompanionTheory.CFin
end

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_points_eq_embedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : GAd σ J), g ∈ ratPts σ J → ∃ η : GRat σ J, g = ratEmb σ J η := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.exists_ratEmb_eq_of_mem_ratPts
end

section
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def swapIdx (r m : ℕ) : Idx r m ≃ Idx r m where
  toFun u := match u with
    | .inl i => .inr (.inr i)
    | .inr (.inl k) => .inr (.inl k)
    | .inr (.inr i) => .inl i
  invFun u := match u with
    | .inl i => .inr (.inr i)
    | .inr (.inl k) => .inr (.inl k)
    | .inr (.inr i) => .inl i
  left_inv u := by rcases u with i | k | i <;> rfl
  right_inv u := by rcases u with i | k | i <;> rfl

theorem lev_swapIdx {r m : ℕ} (S : Finset (Fin r)) (u : Idx r m) : lev m S (swapIdx r m u) = - lev m S u := by
  rcases u with i | k | i <;> simp [lev, swapIdx]

theorem frm_swap {A : Type} {n r m : ℕ} (X : Matrix (Fin n) (Fin r) A) (Z : Matrix (Fin n) (Fin m) A)
    (Y : Matrix (Fin n) (Fin r) A) : frm Y Z X = (frm X Z Y).submatrix id (swapIdx r m) := by
  ext a u
  rcases u with i | k | i <;> rfl

theorem bd_eq_self {L : Type} [Field L] (s : L →+* L) (hs : ∀ x, s (s x) = x) {n r m : ℕ}
    {J : Matrix (Fin n) (Fin n) L} {X Y : Matrix (Fin n) (Fin r) L} {Z : Matrix (Fin n) (Fin m) L}
    {Qi : Matrix (Idx r m) (Fin n) L} (hJ : cT s J = J) (xx : cT s X * J * X = 0) (yy : cT s Y * J * Y = 0)
    (xy : cT s X * J * Y = 1) (xz : cT s X * J * Z = 0) (yz : cT s Y * J * Z = 0)
    (hl : Qi * frm X Z Y = 1) (hr : frm X Z Y * Qi = 1) (S : Finset (Fin r)) {g : Matrix (Fin n) (Fin n) L}
    (hg : IsUnit g) (hu : cT s g * J * g = J) (h1 : ∀ j ∈ S, StabUpTo X g j) (h2 : ∀ j ∈ S, StabUpTo Y g j) :
    bd (lev m S) (Qi * g * frm X Z Y) = Qi * g * frm X Z Y := by
  have yx : cT s Y * J * X = 1 := by
    have cc : ∀ W : Matrix (Fin n) (Fin r) L, cT s (cT s W) = W := fun W => Matrix.ext fun i j => hs _
    have := congrArg (cT s) xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  let sw := swapIdx r m
  have a1 : (Qi.submatrix sw id) * frm Y Z X = 1 := by
    rw [frm_swap, ← Matrix.submatrix_mul _ _ sw id sw Function.bijective_id, hl, Matrix.submatrix_one_equiv]
  have a2 : frm Y Z X * (Qi.submatrix sw id) = 1 := by
    rw [frm_swap, Matrix.submatrix_mul_equiv, hr]; rfl
  have b1 := GlobalTheory.T.frame_stabilizer_flag_criterion L s hs n r m J X Y Z Qi hJ xx yy xy xz yz hl hr S g hg hu h1
  have b2 := GlobalTheory.T.frame_stabilizer_flag_criterion L s hs n r m J Y X Z (Qi.submatrix sw id) hJ yy xx yx yz xz a1 a2 S g hg hu h2
  ext u v
  simp only [bd, Matrix.of_apply]
  split_ifs with h
  · rfl
  rcases lt_or_gt_of_ne h with h3 | h3
  · have h4 : lev m S (sw v) < lev m S (sw u) := by
      rw [lev_swapIdx, lev_swapIdx]; omega
    have := b2 (i := sw u) (j := sw v) h4
    rw [frm_swap] at this
    have e : (Qi.submatrix sw id * g * (frm X Z Y).submatrix id sw) (sw u) (sw v) = (Qi * g * frm X Z Y) (sw (sw u)) (sw (sw v)) := by
      simp [Matrix.mul_apply, Matrix.submatrix_apply]
    have e2 : ∀ w, sw (sw w) = w := fun w => (swapIdx r m).symm_apply_apply w
    rw [e, e2, e2] at this
    exact this.symm
  · exact (b1 h3).symm

section Levi

variable {σ : E →ₐ[F] E} {n r m : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
  {Z : Matrix (Fin n) (Fin m) E} {Qi : Matrix (Idx r m) (Fin n) E}

theorem block_frame_conjugation_identity {G : Type} [Group G] (a b c : G) : (a * b⁻¹) * c * (a * b⁻¹)⁻¹ = a * (b⁻¹ * c * b) * a⁻¹ := by group

theorem mul_eq_mul_conj_alt {G : Type} [Group G] (a b : G) : a * b = b * (b⁻¹ * a * b) := by group

omit [NumberField F] [NumberField E] in
theorem coord_mul (hr : frm X Z Y * Qi = 1) (a b : Matrix (Fin n) (Fin n) E) :
    Qi * (a * b) * frm X Z Y = (Qi * a * frm X Z Y) * (Qi * b * frm X Z Y) := by
  calc Qi * (a * b) * frm X Z Y = Qi * (a * (frm X Z Y * Qi) * b) * frm X Z Y := by rw [hr, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_conj_levi (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (xz : cT (σ : E →+* E) X * J * Z = 0) (yz : cT (σ : E →+* E) Y * J * Z = 0)
    (hl : Qi * frm X Z Y = 1) (hr : frm X Z Y * Qi = 1) (S : Finset (Fin r)) (δ : GRat σ J)
    (hδ : GlobalTheory.Orb.IsRegSS δ.1.1) (hst : ∀ j ∈ S, StabUpTo X δ.1.1 j) :
    ∃ δ' : GRat σ J, IsConj δ δ' ∧ Qi * δ'.1.1 * frm X Z Y = bd (lev m S) (Qi * δ.1.1 * frm X Z Y) := by
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := sigma_sigma h
  have hJ' : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 _ _
  have tri := fun (g : GRat σ J) (hg : ∀ j ∈ S, StabUpTo X g.1.1 j) =>
    GlobalTheory.T.frame_stabilizer_flag_criterion E (σ : E →+* E) hs n r m J X Y Z Qi hJ' hW.xx hW.yy hW.xy xz yz hl hr S g.1.1 g.1.isUnit g.2 hg
  obtain ⟨g, hg, hμ⟩ := GlobalTheory.T.regular_semisimple_flag_stabilizer F E σ h n J hJ r X Y hW S δ hδ hst
  obtain ⟨μ, hμdef⟩ : ∃ μ : GRat σ J, μ = g⁻¹ * δ * g := ⟨_, rfl⟩
  rw [← hμdef] at hμ
  have hμb : bd (lev m S) (Qi * μ.1.1 * frm X Z Y) = Qi * μ.1.1 * frm X Z Y :=
    bd_eq_self (σ : E →+* E) hs hJ' hW.xx hW.yy hW.xy xz yz hl hr S μ.1.isUnit μ.2
      (fun j hj => (hμ j hj).1) (fun j hj => (hμ j hj).2)
  have tg := tri g hg
  have tδ := tri δ hst
  have tμ : (Qi * μ.1.1 * frm X Z Y).BlockTriangular (lev m S) := tri μ fun j hj => (hμ j hj).1
  have rel : δ * g = g * μ := by rw [hμdef]; exact mul_eq_mul_conj_alt δ g
  have cm : ∀ a b : GRat σ J, Qi * (a * b).1.1 * frm X Z Y = (Qi * a.1.1 * frm X Z Y) * (Qi * b.1.1 * frm X Z Y) :=
    fun a b => coord_mul hr a.1.1 b.1.1
  have rel' : (Qi * δ.1.1 * frm X Z Y) * (Qi * g.1.1 * frm X Z Y) = (Qi * g.1.1 * frm X Z Y) * (Qi * μ.1.1 * frm X Z Y) := by
    rw [← cm, ← cm, rel]
  have rel2 := congrArg (bd (lev m S)) rel'
  rw [bd_mul tδ tg, bd_mul tg tμ, hμb] at rel2
  obtain ⟨hU, hUJ⟩ := GlobalTheory.T.frame_stabilizer_flag_converse E (σ : E →+* E) hs n r m J X Y Z Qi hJ' hW.xx hW.yy hW.xy xz yz hl hr S g.1.1
    g.1.isUnit g.2 tg
  obtain ⟨g', hg'def⟩ : ∃ g' : GRat σ J, g'.1.1 = frm X Z Y * bd (lev m S) (Qi * g.1.1 * frm X Z Y) * Qi :=
    ⟨⟨hU.unit, hUJ⟩, rfl⟩
  set B := bd (lev m S) (Qi * g.1.1 * frm X Z Y) with hB
  have hg' : Qi * g'.1.1 * frm X Z Y = B := by
    rw [hg'def]
    calc _ = (Qi * frm X Z Y) * B * (Qi * frm X Z Y) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hl, Matrix.one_mul, Matrix.mul_one]
  have e3 : B * (Qi * (g'⁻¹).1.1 * frm X Z Y) = 1 := by
    rw [← hg', ← cm, mul_inv_cancel]
    change Qi * 1 * frm X Z Y = 1
    rw [Matrix.mul_one, hl]
  have conj : (g' * g⁻¹) * δ * (g' * g⁻¹)⁻¹ = g' * μ * g'⁻¹ := by rw [hμdef]; exact block_frame_conjugation_identity g' g δ
  refine ⟨g' * μ * g'⁻¹, isConj_iff.2 ⟨g' * g⁻¹, conj⟩, ?_⟩
  have e1 : (g' * μ * g'⁻¹) * g' = g' * μ := inv_mul_cancel_right _ _
  have e2 : (Qi * (g' * μ * g'⁻¹).1.1 * frm X Z Y) * B = B * (Qi * μ.1.1 * frm X Z Y) := by
    rw [← hg', ← cm, ← cm, e1]
  calc Qi * (g' * μ * g'⁻¹).1.1 * frm X Z Y
      = (Qi * (g' * μ * g'⁻¹).1.1 * frm X Z Y) * B * (Qi * (g'⁻¹).1.1 * frm X Z Y) := by
        rw [Matrix.mul_assoc _ B, e3, Matrix.mul_one]
    _ = bd (lev m S) (Qi * δ.1.1 * frm X Z Y) * B * (Qi * (g'⁻¹).1.1 * frm X Z Y) := by
        rw [e2, rel2]
    _ = _ := by rw [Matrix.mul_assoc, e3, Matrix.mul_one]

end Levi

section Arch

variable {σ : E →ₐ[F] E} {n r m : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
  {Z : Matrix (Fin n) (Fin m) E} {Qi : Matrix (Idx r m) (Fin n) E}

omit [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] in

theorem norm_matrix_triple_product_le {a b c d : Type} [Fintype b] [Fintype c] (A : Matrix a b ℂ) (M : Matrix b c ℂ)
    (B : Matrix c d ℂ) {α μ β : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ α) (hM : ∀ i j, ‖M i j‖ ≤ μ) (hB : ∀ i j, ‖B i j‖ ≤ β)
    (i : a) (j : d) : ‖(A * M * B) i j‖ ≤ Fintype.card b * Fintype.card c * (α * μ * β) :=
  _root_.UpperTheory.Reformulated.B.Yla6.main A M B hA hM hB i j

omit [Field F] [NumberField F] [Algebra F E] in

theorem entry_le_sum {a b : Type} [Fintype a] [Fintype b] (M : Matrix a b E) (φ : E →+* ℂ) (i : a) (j : b) :
    ‖φ (M i j)‖ ≤ ∑ ψ : E →+* ℂ, ∑ u, ∑ v, ‖ψ (M u v)‖ :=
  ((Finset.single_le_sum (f := fun v => ‖φ (M i v)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun u => ∑ v, ‖φ (M u v)‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ i))).trans
    (Finset.single_le_sum (f := fun ψ : E →+* ℂ => ∑ u, ∑ v, ‖ψ (M u v)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ φ))

theorem block_diagonal_bound_weighted : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → ℤ) (P P' M : Matrix ι ι ℂ) (w : ι → ℝ) (B R : ℝ), (∀ u, 0 < w u) → P * P' = 1 → P.BlockTriangular b → (P * diagonal (fun u => (w u : ℂ)) * M * diagonal (fun u => (((w u)⁻¹ : ℝ) : ℂ)) * P').BlockTriangular b → (∀ u v, ‖P u v‖ ≤ B) → (∀ u v, ‖P' u v‖ ≤ B) → (∀ u v, ‖M u v‖ ≤ B) → (∀ u v, b u = b v → w u ≤ R * w v) → ∀ u v, ‖bd b (P * diagonal (fun u => (w u : ℂ)) * M * diagonal (fun u => (((w u)⁻¹ : ℝ) : ℂ)) * P') u v‖ ≤ (Fintype.card ι : ℝ) ^ 2 * B ^ 3 * R := by
  intro ι _ _ b P P' M w B R hw hPP hP hN hBP hBP' hBM hR u v
  set T := diagonal (fun u => (w u : ℂ)) * M * diagonal (fun u => (((w u)⁻¹ : ℝ) : ℂ)) with hTd
  have hdet : IsUnit P.det := Matrix.isUnit_det_of_right_inverse hPP
  have hinv : P⁻¹ = P' := Matrix.inv_eq_right_inv hPP
  have hP'P : P' * P = 1 := by rw [← hinv]; exact Matrix.nonsing_inv_mul P hdet
  have hP' : P'.BlockTriangular b := by
    haveI := P.invertibleOfIsUnitDet hdet
    rw [← hinv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hP
  have e : P * diagonal (fun u => (w u : ℂ)) * M * diagonal (fun u => (((w u)⁻¹ : ℝ) : ℂ)) * P' = P * T * P' := by
    simp only [hTd, Matrix.mul_assoc]
  rw [e] at hN ⊢
  have hT : T.BlockTriangular b := by
    have e2 : T = P' * (P * T * P') * P := by
      calc T = (P' * P) * T * (P' * P) := by rw [hP'P, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e2]
    exact (hP'.mul hN).mul hP
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hBM u u)
  have hR0 : 0 ≤ R := by
    have h1 := hR u u rfl
    by_contra hneg
    push_neg at hneg
    nlinarith [hw u]
  rw [bd_mul (hP.mul hT) hP', bd_mul hP hT]
  have hbP : ∀ x y, ‖bd b P x y‖ ≤ B := fun x y => by
    simp only [bd, Matrix.of_apply]
    split_ifs
    · exact hBP x y
    · simpa using hB0
  have hbP' : ∀ x y, ‖bd b P' x y‖ ≤ B := fun x y => by
    simp only [bd, Matrix.of_apply]
    split_ifs
    · exact hBP' x y
    · simpa using hB0
  have hbT : ∀ x y, ‖bd b T x y‖ ≤ B * R := fun x y => by
    simp only [bd, Matrix.of_apply]
    split_ifs with hxy
    · have eT : T x y = (w x : ℂ) * M x y * (((w y)⁻¹ : ℝ) : ℂ) := by
        simp only [hTd, Matrix.mul_diagonal, Matrix.diagonal_mul]
      rw [eT, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hw x).le,
        Real.norm_of_nonneg (inv_nonneg.2 (hw y).le)]
      have h1 := hR x y hxy
      have hwy := hw y
      calc w x * ‖M x y‖ * (w y)⁻¹ ≤ (R * w y) * B * (w y)⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 (hBM x y) (norm_nonneg _) ((hw x).le.trans h1))
              (inv_nonneg.2 hwy.le)
        _ = B * R := by field_simp
    · simpa using mul_nonneg hB0 hR0
  have := norm_matrix_triple_product_le (bd b P) (bd b T) (bd b P') hbP hbT hbP' u v
  refine this.trans (le_of_eq ?_)
  ring

theorem parabolic_triangular_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (Z : Matrix (Fin n) (Fin m) E) (Qi : Matrix (Idx r m) (Fin n) E), IsHermND σ J → IsWittFrame σ J X Y → cT (σ : E →+* E) X * J * Z = 0 → cT (σ : E →+* E) Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ p ∈ minParOne σ J X, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (S : Finset (Fin r)), (Qi.map τ.1 * archMat σ J τ (projArch σ J w p) * (frm X Z Y).map τ.1).BlockTriangular (lev m S) := by
  intro F E _ _ _ _ _ σ h n r m J X Y Z Qi hJ hW xz yz hl hr p hp w τ S
  have cTm : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) E),
      cT (starRingEnd ℂ) (A.map τ.1) = (cT (σ : E →+* E) A).map τ.1 :=
    fun A => Matrix.ext fun i j => (h.2.2.2 τ.1 (A j i)).symm
  have rel : ∀ {a b : ℕ} (A : Matrix (Fin n) (Fin a) E) (B : Matrix (Fin n) (Fin b) E) (M : Matrix (Fin a) (Fin b) E),
      cT (σ : E →+* E) A * J * B = M → cT (starRingEnd ℂ) (A.map τ.1) * J.map τ.1 * B.map τ.1 = M.map τ.1 :=
    fun A B M e => by rw [cTm, ← Matrix.map_mul, ← Matrix.map_mul, e]
  have hfrm : frm (X.map τ.1) (Z.map τ.1) (Y.map τ.1) = (frm X Z Y).map τ.1 := by
    ext a u
    rcases u with i | k | i <;> rfl
  have one_map : ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ((1 : Matrix ι ι E).map τ.1) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have zero_map : ∀ {a b : Type}, ((0 : Matrix a b E).map τ.1) = 0 := Matrix.map_zero _ (map_zero _)
  have hJc : cT (starRingEnd ℂ) (J.map τ.1) = J.map τ.1 := by
    rw [cTm]; exact congrArg (Matrix.map · τ.1) (Matrix.ext fun i j => hJ.1 _ _)
  have hl' : Qi.map τ.1 * frm (X.map τ.1) (Z.map τ.1) (Y.map τ.1) = 1 := by
    rw [hfrm, ← Matrix.map_mul, hl, one_map]
  have hr' : frm (X.map τ.1) (Z.map τ.1) (Y.map τ.1) * Qi.map τ.1 = 1 := by
    rw [hfrm, ← Matrix.map_mul, hr, one_map]
  have t := GlobalTheory.T.frame_stabilizer_flag_criterion ℂ (starRingEnd ℂ) (fun x => star_star x) n r m (J.map τ.1) (X.map τ.1) (Y.map τ.1)
    (Z.map τ.1) (Qi.map τ.1) hJc ((rel X X 0 hW.xx).trans zero_map) ((rel Y Y 0 hW.yy).trans zero_map)
    ((rel X Y 1 hW.xy).trans one_map) ((rel X Z 0 xz).trans zero_map) ((rel Y Z 0 yz).trans zero_map) hl' hr' S
    (archMat σ J τ (projArch σ J w p)) ((Group.isUnit (projArch σ J w p)).map (archMat σ J τ))
    (GlobalTheory.T.archimedean_matrix_preserves_form F E σ h n J p w τ) (fun j _ => GlobalTheory.T.minimal_parabolic_archimedean_stabilizes F E σ h n r J X p hp w τ j)
  rwa [hfrm] at t

theorem arch_bound (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    (xz : cT (σ : E →+* E) X * J * Z = 0) (yz : cT (σ : E →+* E) Y * J * Z = 0)
    (hl : Qi * frm X Z Y = 1) (hr : frm X Z Y * Qi = 1) {Ω C₁ : Set (GAd σ J)} (hΩ : IsCompact Ω)
    (hΩP : Ω ⊆ minParOne σ J X) (hC₁ : IsCompact C₁) (R : ℝ) :
    ∃ B : ℝ, ∀ p ∈ Ω, ∀ t : Fin r → ℝ, (∀ i, 0 < t i) → ∀ a, IsTorusElt σ J X Y t a → ∀ y ∈ C₁,
      ∀ S : Finset (Fin r), (∀ u v, lev m S u = lev m S v → wt m t u ≤ R * wt m t v) →
      ∀ δ : GRat σ J, ratEmb σ J δ = p * a * y * a⁻¹ * p⁻¹ → (∀ j ∈ S, StabUpTo X δ.1.1 j) →
      ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : Idx r m),
        ‖τ.1 (bd (lev m S) (Qi * δ.1.1 * frm X Z Y) u v)‖ ≤ B := by
  obtain ⟨Bp, -, hBp⟩ := GlobalTheory.T.compact_archimedean_entries_bounded F E σ n J Ω hΩ
  obtain ⟨Bpi, -, hBpi⟩ := GlobalTheory.T.compact_archimedean_entries_bounded F E σ n J (Inv.inv '' Ω) (hΩ.image continuous_inv)
  obtain ⟨By, -, hBy⟩ := GlobalTheory.T.compact_archimedean_entries_bounded F E σ n J C₁ hC₁
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := sigma_sigma h
  have hJ' : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 _ _
  set q1 := ∑ ψ : E →+* ℂ, ∑ u, ∑ v, ‖ψ (Qi u v)‖ with hq1
  set q2 := ∑ ψ : E →+* ℂ, ∑ u, ∑ v, ‖ψ (frm X Z Y u v)‖ with hq2
  have q1n : 0 ≤ q1 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have q2n : 0 ≤ q2 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set b0 := (n : ℝ) * n * (q1 * max Bp (max Bpi By) * q2) with hb0
  refine ⟨(Fintype.card (Idx r m) : ℝ) ^ 2 * b0 ^ 3 * R, ?_⟩
  intro p hp t ht a ha y hy S hR δ hδ hst w τ u v
  set φ : E →+* ℂ := τ.1 with hφ
  set Qc := (frm X Z Y).map φ with hQc
  set Qic := Qi.map φ with hQic
  have hlc : Qic * Qc = 1 := by rw [hQic, hQc, ← Matrix.map_mul, hl, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hrc : Qc * Qic = 1 := by rw [hQic, hQc, ← Matrix.map_mul, hr, Matrix.map_one _ (map_zero φ) (map_one φ)]
  set am : GAd σ J → Matrix (Fin n) (Fin n) ℂ := fun g => archMat σ J τ (projArch σ J w g) with ham
  have amul : ∀ g g', am (g * g') = am g * am g' := fun g g' => by simp only [ham, map_mul]
  have aone : am 1 = 1 := by simp only [ham, map_one]
  have ainv : ∀ g, am g * am g⁻¹ = 1 := fun g => by rw [← amul, mul_inv_cancel, aone]
  have ainv' : ∀ g, am g⁻¹ * am g = 1 := fun g => by rw [← amul, inv_mul_cancel, aone]
  set cd : Matrix (Fin n) (Fin n) ℂ → Matrix (Idx r m) (Idx r m) ℂ := fun M => Qic * M * Qc with hcd
  have cmul : ∀ M M', cd (M * M') = cd M * cd M' := fun M M' => by
    simp only [hcd]
    calc Qic * (M * M') * Qc = Qic * (M * (Qc * Qic) * M') * Qc := by rw [hrc, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have cone' : cd 1 = 1 := by simp only [hcd, Matrix.mul_one, hlc]
  have hD : (Qi * δ.1.1 * frm X Z Y).map φ = cd (am p) * cd (am a) * cd (am y) * cd (am a⁻¹) * cd (am p⁻¹) := by
    have e : δ.1.1.map φ = am (ratEmb σ J δ) := (GlobalTheory.T.archimedean_rational_embedding_map F E σ n J δ w τ).symm
    rw [Matrix.map_mul, Matrix.map_mul, e, hδ, amul, amul, amul, amul, ← hQic, ← hQc]
    change cd _ = _
    rw [cmul, cmul, cmul, cmul]
  have htor : am a * Qc = Qc * diagonal (fun u => ((wt m t u : ℝ) : ℂ)) := GlobalTheory.T.torus_archimedean_frame_conjugation F E σ n r m J X Y Z xz yz t a ha w τ
  have wpos : ∀ u, 0 < wt m t u := fun u => by rcases u with i | k | i <;> simp [wt, ht]
  have dd : diagonal (fun u => ((wt m t u : ℝ) : ℂ)) * diagonal (fun u => (((wt m t u)⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext u
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (wpos u).ne', Complex.ofReal_one]
  have ca : cd (am a) = diagonal (fun u => ((wt m t u : ℝ) : ℂ)) := by
    simp only [hcd]; rw [Matrix.mul_assoc, htor, ← Matrix.mul_assoc, hlc, Matrix.one_mul]
  have cai : cd (am a⁻¹) = diagonal (fun u => (((wt m t u)⁻¹ : ℝ) : ℂ)) := by
    have e : cd (am a⁻¹) * cd (am a) = 1 := by rw [← cmul, ainv', cone']
    calc cd (am a⁻¹) = cd (am a⁻¹) * (diagonal (fun u => ((wt m t u : ℝ) : ℂ)) * diagonal (fun u => (((wt m t u)⁻¹ : ℝ) : ℂ))) := by
          rw [dd, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, ← ca, e, Matrix.one_mul]
  rw [ca, cai] at hD
  have bM : ∀ (g : GAd σ J) (β : ℝ), (∀ i j, ‖am g i j‖ ≤ β) → β ≤ max Bp (max Bpi By) → ∀ i j, ‖cd (am g) i j‖ ≤ b0 :=
    fun g β hg hβ i j => by
      have := norm_matrix_triple_product_le Qic (am g) Qc (fun i j => entry_le_sum Qi φ i j) hg (fun i j => entry_le_sum (frm X Z Y) φ i j) i j
      simp only [Fintype.card_fin] at this
      refine this.trans ?_
      rw [hb0]
      gcongr
  have b1 := bM p Bp (fun i j => hBp p hp w τ i j) (le_max_left _ _)
  have b2 := bM p⁻¹ Bpi (fun i j => hBpi p⁻¹ ⟨p, hp, rfl⟩ w τ i j) ((le_max_left _ _).trans (le_max_right _ _))
  have b3 := bM y By (fun i j => hBy y hy w τ i j) ((le_max_right _ _).trans (le_max_right _ _))
  have tP := parabolic_triangular_frame F E σ h n r m J X Y Z Qi hJ hW xz yz hl hr p (hΩP hp) w τ S
  have tN : ((Qi * δ.1.1 * frm X Z Y).map φ).BlockTriangular (lev m S) := by
    have t0 := GlobalTheory.T.frame_stabilizer_flag_criterion E (σ : E →+* E) hs n r m J X Y Z Qi hJ' hW.xx hW.yy hW.xy xz yz hl hr S δ.1.1
      δ.1.isUnit δ.2 hst
    intro i j hij
    simp only [Matrix.map_apply, t0 hij, map_zero]
  have hPP : cd (am p) * cd (am p⁻¹) = 1 := by rw [← cmul, ainv, cone']
  rw [hD] at tN
  have := block_diagonal_bound_weighted (lev m S) (cd (am p)) (cd (am p⁻¹)) (cd (am y)) (wt m t) b0 R wpos hPP tP tN b1 b2 b3 hR u v
  rw [← hD, ← bd_map _ _ (map_zero φ)] at this
  exact this

end Arch

section Classes

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField F] [NumberField E] in

theorem isRegSS_of_isConj {γ δ : GRat σ J} (hc : IsConj γ δ) (hγ : GlobalTheory.Orb.IsRegSS γ.1.1) :
    GlobalTheory.Orb.IsRegSS δ.1.1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  have e : (c * γ * c⁻¹).1.1 = (c.1 : GL (Fin n) E).1 * γ.1.1 * ((c.1)⁻¹ : GL (Fin n) E).1 := rfl
  unfold GlobalTheory.Orb.IsRegSS at *
  rw [e, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  exact hγ

theorem classes_finite (hS : PositivityTheory.ThKR.SiegelCore) (h : IsCMExt F E σ) (hJ : IsHermND σ J) {C : Set (GAd σ J)}
    (hC : IsCompact C) :
    {𝔬 : Set (GRat σ J) | (∃ γ : GRat σ J, GlobalTheory.Orb.IsRegSS γ.1.1 ∧ 𝔬 = {δ | IsConj γ δ}) ∧
      ∃ (x : GAd σ J) (δ : GRat σ J), δ ∈ 𝔬 ∧ x⁻¹ * ratEmb σ J δ * x ∈ C}.Finite := by
  classical
  obtain ⟨r, X, Y, hW⟩ := exists_isWittFrame h hJ
  obtain ⟨m, Z, Qi, xz, yz, hl, hr⟩ := GlobalTheory.T.exists_witt_complement_frame F E σ h n J hJ r X Y hW
  obtain ⟨K, Ω, c, hK, hΩ, hΩP, hc, -, -, hcov, -, -, -⟩ := hS F E σ h n J hJ r X Y hW
  have hcont : Continuous fun q : GAd σ J × GAd σ J => q.1 * q.2 * q.1⁻¹ :=
    (continuous_fst.mul continuous_snd).mul continuous_fst.inv
  set C₁ : Set (GAd σ J) := (fun q : GAd σ J × GAd σ J => q.1 * q.2 * q.1⁻¹) '' ((K : Set (GAd σ J)) ×ˢ C) with hC₁d
  have hC₁ : IsCompact C₁ := (hK.prod hC).image hcont
  obtain ⟨t0, ht0⟩ := GlobalTheory.T.siegel_compact_translate_bound F E σ h n J hJ r X Y hW Ω hΩ hΩP K hK c hc C hC
  obtain ⟨R, -, hR⟩ := GlobalTheory.T.deep_cone_weight_ratio_bound r m c (max t0 1) hc (le_max_right _ _)
  obtain ⟨B, hB⟩ := arch_bound (Z := Z) h hJ hW xz yz hl hr hΩ hΩP hC₁ R
  set 𝒞 : Set (GFin σ J) := projFin σ J '' ((fun q : GAd σ J × GAd σ J => q.1 * q.2 * q.1⁻¹) '' (Ω ×ˢ C₁)) with h𝒞d
  have h𝒞 : IsCompact 𝒞 := ((hΩ.prod hC₁).image hcont).image (continuous_projFin σ J)
  obtain ⟨dd, hdd, hint⟩ := GlobalTheory.T.compact_finite_rational_denominator F E σ n J 𝒞 h𝒞 Qi (frm X Z Y)
  have hfin := GlobalTheory.T.bounded_integral_matrices_finite F E h.1 (ι := Idx r m) dd B hdd
  have recon : ∀ M : Matrix (Fin n) (Fin n) E, frm X Z Y * (Qi * M * frm X Z Y) * Qi = M := fun M => by
    calc frm X Z Y * (Qi * M * frm X Z Y) * Qi = (frm X Z Y * Qi) * M * (frm X Z Y * Qi) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hr, Matrix.one_mul, Matrix.mul_one]
  have hinj : Set.InjOn (fun δ : GRat σ J => Qi * δ.1.1 * frm X Z Y) ((fun δ : GRat σ J => Qi * δ.1.1 * frm X Z Y) ⁻¹'
      {N : Matrix (Idx r m) (Idx r m) E | (∀ u v, IsIntegral ℤ ((dd : E) * N u v)) ∧
        ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : Idx r m), ‖τ.1 (N u v)‖ ≤ B}) := by
    intro δ _ δ' _ e
    have e' : δ.1.1 = δ'.1.1 := by rw [← recon δ.1.1, ← recon δ'.1.1]; exact congrArg (fun M => frm X Z Y * M * Qi) e
    exact Subtype.ext (Units.ext e')
  refine ((hfin.preimage hinj).image fun δ' => {δ | IsConj δ' δ}).subset ?_
  rintro 𝔬 ⟨⟨γ, hγ, rfl⟩, x, δ, hδ, hx⟩
  obtain ⟨η, hη, s, hs, rfl⟩ := hcov x
  obtain ⟨η', rfl⟩ := GlobalTheory.T.rational_points_eq_embedding F E σ n J η hη
  obtain ⟨p, hp, t, ht, a, ha, k, hk, rfl⟩ := hs
  obtain ⟨δ₁, hδ₁d⟩ : ∃ δ₁ : GRat σ J, δ₁ = η'⁻¹ * δ * η' := ⟨_, rfl⟩
  have hδ₁ : (p * a * k)⁻¹ * ratEmb σ J δ₁ * (p * a * k) ∈ C := by
    convert hx using 1
    rw [hδ₁d, map_mul, map_mul, map_inv]
    group
  have hst : ∀ j ∈ deep (max t0 1) t, StabUpTo X δ₁.1.1 j := by
    intro j hj
    simp only [deep, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ht0 p hp t ht a ha k hk δ₁ hδ₁ j (lt_of_le_of_lt (le_max_left _ _) hj.1)
      (fun j' e => lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _) (ht.1 j').le) (hj.2 j' e))
  have c1 : IsConj γ δ₁ := (show IsConj γ δ from hδ).trans (isConj_iff.2 ⟨η'⁻¹, by rw [hδ₁d, inv_inv]⟩)
  obtain ⟨δ', hc', hδ'⟩ := exists_conj_levi h hJ hW xz yz hl hr (deep (max t0 1) t) δ₁ (isRegSS_of_isConj c1 hγ) hst
  set δ₀ := (p * a * k)⁻¹ * ratEmb σ J δ₁ * (p * a * k) with hδ₀
  have hy : k * δ₀ * k⁻¹ ∈ C₁ := ⟨(k, δ₀), ⟨hk, hδ₁⟩, rfl⟩
  have hid : ratEmb σ J δ₁ = p * a * (k * δ₀ * k⁻¹) * a⁻¹ * p⁻¹ := by rw [hδ₀]; group
  have hpa : projFin σ J a = 1 := mem_infPts.1 ha.1
  have hf𝒞 : projFin σ J (ratEmb σ J δ₁) ∈ 𝒞 := ⟨p * (k * δ₀ * k⁻¹) * p⁻¹, ⟨(p, k * δ₀ * k⁻¹), ⟨hp, hy⟩, rfl⟩, by
    rw [hid]; simp only [map_mul, map_inv, hpa, mul_one, inv_one]⟩
  refine ⟨δ', ⟨fun u v => ?_, fun w τ u v => ?_⟩, ?_⟩
  · simp only [hδ', bd, Matrix.of_apply]
    split_ifs
    · exact hint δ₁ hf𝒞 u v
    · rw [mul_zero]; exact isIntegral_zero
  · simp only
    rw [hδ']
    exact hB p hp t ht.1 a ha _ hy _ (hR t ht) δ₁ hid hst w τ u v
  · have c2 : IsConj γ δ' := c1.trans hc'
    ext z
    exact ⟨fun hz => c2.trans hz, fun hz => c2.symm.trans hz⟩

end Classes

theorem regClassFin : PositivityTheory.ThKR.SiegelCore → MainStatements.RegularCuspidalTrace.RegClassFin := by
  intro hS D V f hf
  obtain ⟨h, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have hc := (GlobalTheory.Orb.continuous_of_mem_ccAd hf).2
  refine (classes_finite hS h (hJ V) hc.isCompact).subset ?_
  rintro 𝔬 ⟨h1, x, δ, hδ, hx⟩
  exact ⟨h1, x, δ, hδ, subset_tsupport f (Function.mem_support.2 hx)⟩

end GlobalTheory.CompanionTheory.CFin
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_implies_regular_class_finite : PositivityTheory.ThKR.SiegelCore → MainStatements.RegularCuspidalTrace.RegClassFin := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CFin.regClassFin
end
