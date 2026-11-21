import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IrrNormal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LinClosedOfAdic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.StrongIrrOfOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CommonFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RegCoset
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FullEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SepOfMinors
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiagonalEntries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.OneUnitTF
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IrrOfConn
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TwoDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe

section
open Matrix Polynomial

namespace UpperTheory.V.Pr

private lemma diagE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (α : Fin 2 → κ)
    (hα : Function.Injective α) (h : M.charpoly = ∏ i, (X - C (α i))) :
    ∃ P : GL (Fin 2) κ, M * (P : Matrix (Fin 2) (Fin 2) κ) = (P : Matrix (Fin 2) (Fin 2) κ) * diagonal α :=
  _root_.UpperTheory.Reformulated.B.DiagonalizeTwoByTwo.diagE M α hα h

private lemma strongIrr_conjE {G κ : Type} [Group G] [Field κ] {n : ℕ} (r : G →* GL (Fin n) κ) (h : StrongIrr r)
    (P : GL (Fin n) κ) : StrongIrr ((MulAut.conj P⁻¹).toMonoidHom.comp r) := by
  intro W S hS hW
  set A : Matrix (Fin n) (Fin n) κ := (P : Matrix (Fin n) (Fin n) κ) with hA
  set B : Matrix (Fin n) (Fin n) κ := ((P⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) with hB
  have hAB : ∀ v, A *ᵥ (B *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hA, hB, Units.mul_inv, one_mulVec]
  have hBA : ∀ v, B *ᵥ (A *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hA, hB, Units.inv_mul, one_mulVec]
  have hg : ∀ g v, gm ((MulAut.conj P⁻¹).toMonoidHom.comp r) g *ᵥ v = B *ᵥ (gm r g *ᵥ (A *ᵥ v)) := by
    intro g v
    rw [mulVec_mulVec, mulVec_mulVec]
    rfl
  have hm : ∀ v, v ∈ W.comap (Matrix.toLin' B) ↔ B *ᵥ v ∈ W := fun v => by
    rw [Submodule.mem_comap, toLin'_apply]
  have key := h (W.comap (Matrix.toLin' B)) S hS (by
    intro g
    rw [hW g]
    constructor
    · intro h1 v hv
      have := h1 _ ((hm v).1 hv)
      rw [hg, hAB] at this
      exact (hm _).2 this
    · intro h1 v hv
      rw [hg, ← hm]
      exact h1 _ (by rw [hm, hBA]; exact hv))
  rcases key with key | key
  · left
    rw [eq_bot_iff]
    intro v hv
    have : A *ᵥ v ∈ W.comap (Matrix.toLin' B) := by rw [hm, hBA]; exact hv
    rw [key, Submodule.mem_bot] at this
    rw [Submodule.mem_bot, ← hBA v, this, mulVec_zero]
  · right
    rw [eq_top_iff]
    intro v _
    have : A *ᵥ v ∈ W.comap (Matrix.toLin' B) := by rw [key]; trivial
    rwa [hm, hBA] at this

private def blkE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) : Matrix (Fin 3) (Fin 3) κ :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, w]

private lemma charpoly_blkE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) :
    (blkE M w).charpoly = M.charpoly * (X - C w) := by
  simp only [Matrix.charpoly, det_fin_three, det_fin_two]
  simp [blkE, charmatrix_apply]
  ring

private lemma blkE_mul {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) (a : Fin 2 → κ) (c : κ) (m : ℕ)
    (d : Fin 3 → κ) (h0 : d 0 = a 0) (h1 : d 1 = a 1) (h2 : d 2 = c) :
    blkE M w * diagonal d ^ m = blkE (M * diagonal a ^ m) (w * c ^ m) := by
  ext i j
  simp only [diagonal_pow, mul_diagonal, blkE]
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2]

private lemma minor_neE {κ : Type} [Field κ] {n : ℕ} (Y : Matrix (Fin n) (Fin n) κ) (S : Finset (Fin n))
    (h : ∀ v : Fin n → κ, (∀ i ∈ S, (Y *ᵥ v) i = 0) → (∀ i, i ∉ S → v i = 0) → v = 0) :
    (Y.submatrix (Subtype.val : S → Fin n) Subtype.val).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv'⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have := h (fun j => if hj : j ∈ S then v ⟨j, hj⟩ else 0) (by
    intro i hi
    have h1 := congrFun hv' ⟨i, hi⟩
    simp only [mulVec, dotProduct, submatrix_apply, Pi.zero_apply] at h1 ⊢
    refine Eq.trans ?_ h1
    rw [← Finset.sum_subset (Finset.subset_univ S) (by intro x _ hx; rw [dif_neg hx, mul_zero]),
      ← Finset.sum_coe_sort S]
    exact Finset.sum_congr rfl fun x _ => by rw [dif_pos x.2]) (by intro i hi; exact dif_neg hi)
  apply hv
  ext ⟨j, hj⟩
  have h3 := congrFun this j
  simp only [dif_pos hj] at h3
  exact h3

private lemma minor_blkE {κ : Type} [Field κ] (M : Matrix (Fin 2) (Fin 2) κ) (w : κ) (h0 : M 0 0 ≠ 0) (h1 : M 1 1 ≠ 0)
    (hd : M.det ≠ 0) (hw : w ≠ 0) (S : Finset (Fin 3)) :
    ((blkE M w).submatrix (Subtype.val : S → Fin 3) Subtype.val).det ≠ 0 := by
  apply minor_neE
  intro v ha hb
  rw [det_fin_two] at hd
  have e0 : (blkE M w *ᵥ v) 0 = M 0 0 * v 0 + M 0 1 * v 1 := by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]
  have e1 : (blkE M w *ᵥ v) 1 = M 1 0 * v 0 + M 1 1 * v 1 := by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]
  have e2 : (blkE M w *ᵥ v) 2 = w * v 2 := by simp [blkE, mulVec, dotProduct, Fin.sum_univ_three]
  have v2 : v 2 = 0 := by
    by_cases h : (2 : Fin 3) ∈ S
    · have := ha _ h
      rw [e2] at this
      simpa [hw] using this
    · exact hb _ h
  have v01 : v 0 = 0 ∧ v 1 = 0 := by
    by_cases k0 : (0 : Fin 3) ∈ S <;> by_cases k1 : (1 : Fin 3) ∈ S
    · have a0 := ha _ k0
      have a1 := ha _ k1
      rw [e0] at a0
      rw [e1] at a1
      constructor
      · apply mul_left_cancel₀ hd
        linear_combination M 1 1 * a0 - M 0 1 * a1
      · apply mul_left_cancel₀ hd
        linear_combination M 0 0 * a1 - M 1 0 * a0
    · have a0 := ha _ k0
      have a1 := hb _ k1
      rw [e0, a1] at a0
      exact ⟨by simpa [h0] using a0, a1⟩
    · have a0 := hb _ k0
      have a1 := ha _ k1
      rw [e1, a0] at a1
      exact ⟨a0, by simpa [h1] using a1⟩
    · exact ⟨hb _ k0, hb _ k1⟩
  ext i
  fin_cases i
  · exact v01.1
  · exact v01.2
  · exact v2

private lemma diagCaseE (G κ : Type) [Group G] [Field κ] (σ : G →* GL (Fin 2) κ) (ψ₀ : G →* κˣ) (hσ : StrongIrr σ)
    (u : G) (α : Fin 2 → κˣ) (hα : FreeRatios ![α 0, α 1, ψ₀ u])
    (hu : gm σ u = diagonal (fun i => ((α i : κˣ) : κ))) (y : GL (Fin 2) κ) (z : κˣ) :
    ∃ h, (((y : Matrix (Fin 2) (Fin 2) κ) * gm σ h).charpoly * (X - C ((z * ψ₀ h : κˣ) : κ))).Separable := by
  have hα2 : FreeRatios α := by
    intro i j hij m hm
    have := hα i.castSucc j.castSucc (by simpa using hij) m hm
    fin_cases i <;> fin_cases j <;> simpa using this
  obtain ⟨b, hb⟩ := fullEx G κ 2 σ hσ u α hα2 hu
  obtain ⟨m, hm⟩ := expSums κ (Fin 2) (Fin 2) (fun _ => α)
    (fun s i => (y : Matrix (Fin 2) (Fin 2) κ) s i * gm σ b i s) (fun _ => hα2) (by
      intro s
      by_contra hc
      push Not at hc
      have : ∀ i, (y : Matrix (Fin 2) (Fin 2) κ) s i = 0 := fun i =>
        (mul_eq_zero.1 (hc i)).resolve_right (hb i s).1
      exact y.det_ne_zero (det_eq_zero_of_row_eq_zero s this))
  have hpow : ∀ k : ℕ, gm σ (u ^ k) = diagonal (fun i => ((α i : κˣ) : κ)) ^ k := by
    intro k
    rw [← hu]; simp [gm]
  have hmul : ∀ g g', gm σ (g * g') = gm σ g * gm σ g' := by
    intro g g'; simp [gm]
  set M : Matrix (Fin 2) (Fin 2) κ := (y : Matrix (Fin 2) (Fin 2) κ) * gm σ (u ^ m * b) with hM
  have hdiag : ∀ s, M s s ≠ 0 := by
    intro s
    have : M s s = ∑ i, (y : Matrix (Fin 2) (Fin 2) κ) s i * gm σ b i s * ((α i : κˣ) : κ) ^ m := by
      rw [hM, hmul, hpow, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [diagonal_pow, diagonal_mul]
      simp only [Pi.pow_apply]
      ring
    rw [this]; exact hm s
  have hdet : M.det ≠ 0 := by
    have := (y * σ (u ^ m * b)).det_ne_zero
    rwa [Units.val_mul] at this
  obtain ⟨k, hk⟩ := sepOfMinors κ 3 le_rfl (blkE M ((z * ψ₀ (u ^ m * b) : κˣ) : κ)) _ hα
    (minor_blkE M _ (hdiag 0) (hdiag 1) hdet (Units.ne_zero _))
  rw [blkE_mul M _ (fun i => ((α i : κˣ) : κ)) ((ψ₀ u : κˣ) : κ) k _ rfl rfl rfl, charpoly_blkE] at hk
  refine ⟨u ^ m * b * u ^ k, ?_⟩
  rw [hmul, hpow, ← Matrix.mul_assoc, ← hM]
  convert hk using 4
  simp [mul_assoc]

end UpperTheory.V.Pr

theorem UpperTheory.V.Pr.regCosetE :
    UpperTheory.V.Pr.RegCosetE := by
  intro G κ _ _ σ ψ₀ hσ u α hα hu y z
  have hinj : Function.Injective (fun i => ((α i : κˣ) : κ)) := by
    intro i j hij
    by_contra hne
    have := hα i.castSucc j.castSucc (by simpa using hne) 1 one_pos
    have h2 : α i = α j := Units.ext hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨P, hP⟩ := diagE (gm σ u) _ hinj hu
  obtain ⟨h, hh⟩ := diagCaseE G κ _ ψ₀ (strongIrr_conjE σ hσ P) u α hα (by
    simp only [gm] at hP
    simp [gm, Matrix.mul_assoc, hP]) (P⁻¹ * y * P) z
  refine ⟨h, ?_⟩
  convert hh using 2
  rw [← Matrix.charpoly_units_conj P⁻¹]
  congr 1
  simp [gm, Matrix.mul_assoc]
end

section
private theorem exists_element_separating_powers {G K : Type} [Group G] [Field K] (l : ℕ) [Fact l.Prime] [CharP K l] {n : ℕ}
    (ψ : Fin n → G →* (PowerSeries K)ˣ) (N V : Subgroup G) (hV : V.index ≠ 0)
    (hred : ∀ g ∈ N, ∀ a b, PowerSeries.constantCoeff (ψ a g : PowerSeries K) =
      PowerSeries.constantCoeff (ψ b g : PowerSeries K))
    (hsep : ∀ a b, a ≠ b → ∃ g ∈ N, ψ a g ≠ ψ b g) :
    ∃ g ∈ N, g ∈ V ∧ ∀ a b, a ≠ b → ∀ m : ℕ, 0 < m → ψ a g ^ m ≠ ψ b g ^ m := by
  haveI : CharP (PowerSeries K) l := charP_of_injective_ringHom (PowerSeries.C_injective (R := K)) l
  have tf : ∀ g ∈ N, ∀ a b (m : ℕ), 0 < m → (ψ a g / ψ b g) ^ m = 1 → ψ a g / ψ b g = 1 := by
    intro g hg a b m hm h
    apply Units.ext
    apply UpperTheory.V.Pr.T.oneUnitTF l _ m hm.ne'
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
      have hinv : PowerSeries.constantCoeff ((ψ b g)⁻¹ : (PowerSeries K)ˣ).val *
          PowerSeries.constantCoeff ((ψ b g : (PowerSeries K)ˣ) : PowerSeries K) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      have hc : PowerSeries.constantCoeff (((ψ a g / ψ b g : (PowerSeries K)ˣ) : PowerSeries K) - 1) = 0 := by
        rw [map_sub, div_eq_mul_inv, Units.val_mul, map_mul, hred g hg a b, mul_comm, hinv, map_one, sub_self]
      rw [hc]
      exact not_isUnit_zero
    · rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  let χ : {p : Fin n × Fin n // p.1 ≠ p.2} → ↥(N ⊓ V) →* (PowerSeries K)ˣ :=
    fun p => (ψ p.1.1 / ψ p.1.2).comp (N ⊓ V).subtype
  obtain ⟨h, hh⟩ := UpperTheory.V.Pr.commonFree ↥(N ⊓ V) (PowerSeries K)ˣ {p : Fin n × Fin n // p.1 ≠ p.2} χ 1 one_pos
    (by
      intro p h m hm hpow
      rw [pow_one]
      exact tf h (Subgroup.mem_inf.mp h.2).1 _ _ m hm hpow)
    (by
      intro p
      obtain ⟨g, hgN, hne⟩ := hsep _ _ p.2
      obtain ⟨k, hk, -, hkV⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hV g
      refine ⟨⟨g ^ k, Subgroup.mem_inf.mpr ⟨N.pow_mem hgN k, hkV⟩⟩, ?_⟩
      rw [pow_one]
      intro h1
      apply hne
      have h2 : (ψ p.1.1 g / ψ p.1.2 g) ^ k = 1 := by
        simpa [χ, div_pow, map_pow] using h1
      exact div_eq_one.mp (tf g hgN _ _ k hk h2))
  refine ⟨h, (Subgroup.mem_inf.mp h.2).1, (Subgroup.mem_inf.mp h.2).2, ?_⟩
  intro a b hab m hm heq
  apply hh ⟨(a, b), hab⟩ m hm
  simp [χ, div_pow, heq]

theorem UpperTheory.V.Pr.niceSep :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → ∀ U : Subgroup T.G.G₀, IsOpen (U : Set T.G.G₀) → ∀ v, ∃ g : T.G.Gv v, T.G.φ v g ∈ U ⊓ T.G.G' ∧ UpperTheory.V.Pr.FreeRatios fun i => y.ψ v i g |> Units.map (algebraMap y.A y.Fr).toMonoidHom := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hnice hmat hψ U hU v
  haveI : CharP (IsLocalRing.ResidueField O) l := UpperTheory.V.Fr.IsCoef.char
  haveI : CharP y.K l :=
    charP_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField O) y.K).injective l
  let N : Subgroup (T.G.Gv v) := (F.Nv (T.K.e v)).comap (T.K.lam v).toMonoidHom
  let V : Subgroup (T.G.Gv v) := U.comap (T.G.φ v)
  have hV : V.index ≠ 0 := by
    rw [Subgroup.index_ne_zero_iff_finite]
    exact Subgroup.quotient_finite_of_isOpen V (hU.preimage (T.G.φ_cont v))
  have hred : ∀ g ∈ N, ∀ a b, PowerSeries.constantCoeff (y.ψ v a g : PowerSeries y.K) =
      PowerSeries.constantCoeff (y.ψ v b g : PowerSeries y.K) := by
    intro g hg a b
    have key : ∀ i, PowerSeries.constantCoeff (y.ψ v i g : PowerSeries y.K) =
        algebraMap (IsLocalRing.ResidueField O) y.K (T.r.psib v i g : IsLocalRing.ResidueField O) :=
      fun i => congrArg Units.val (DFunLike.congr_fun (y.ψ_red v i) g)
    have hΨ : F.Ψ ((F.loc0 (T.K.e v) (T.K.lam v g) : F.del.ker) : F.Γ) = 1 :=
      T.ok.Ψ_N (T.K.e v) (T.K.lam v g) hg
    rw [key a, key b, T.K.psib, T.K.psib, T.K.chib, T.K.chib, ← T.K.lam_loc, hΨ, one_zpow, one_zpow]
  have hsep : ∀ a b, a ≠ b → ∃ g ∈ N, y.ψ v a g ≠ y.ψ v b g := by
    intro a b hab
    have hc := hnice.sep (T.K.e v) a b hab
    simp only [UpperTheory.V.Fr.NRep.Coin, not_forall] at hc
    obtain ⟨g', hg', hne⟩ := hc
    refine ⟨(T.K.lam v).symm g', ?_, ?_⟩
    · show (T.K.lam v) ((T.K.lam v).symm g') ∈ F.Nv (T.K.e v)
      simpa using hg'
    · intro heq
      apply hne
      rw [hψ] at heq
      simp only [UpperTheory.V.Pr.TwLink.twψ, MonoidHom.mul_apply, MonoidHom.comp_apply] at heq
      have h2 := congrArg Units.val (mul_right_cancel heq)
      simp [UpperTheory.V.Fr.NRep.map] at h2
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      convert h2 using 4
      all_goals exact ((T.K.lam v).apply_symm_apply g').symm
  obtain ⟨g, hgN, hgV, hfree⟩ := exists_element_separating_powers l (y.ψ v) N V hV hred hsep
  refine ⟨g, ⟨hgV, ?_⟩, ?_⟩
  · show T.G.ε ((T.G.φ v g : T.G.η.ker) : T.G.Γ) = 1
    rw [← T.K.π_eps, ← T.K.lam_loc]
    exact (Subgroup.mem_inf.mp hgN).2
  · intro a b hab m hm heq
    apply hfree a b hab m hm
    apply Units.ext
    apply IsFractionRing.injective y.A y.Fr
    have h2 := congrArg Units.val heq
    simpa [Units.val_pow_eq_pow_val, map_pow] using h2
end
