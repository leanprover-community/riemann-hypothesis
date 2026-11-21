import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtensionProductDecomposition
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlPiEquivSymmContinuous

section
noncomputable section

open Matrix Polynomial ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped Classical

namespace GlobalTheory.CentValHom

theorem eq_diagonal_of_commute {F : Type*} [Field F] {n : ℕ} (lam : Fin n → F)
    (hlam : Function.Injective lam) (W : Matrix (Fin n) (Fin n) F)
    (h : W * diagonal lam = diagonal lam * W) : W = diagonal (fun i => W i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · have h1 := congrFun (congrFun h i) j
    rw [mul_diagonal, diagonal_mul] at h1
    rw [diagonal_apply_ne _ hij]
    have hne : lam j - lam i ≠ 0 := sub_ne_zero.2 (fun e => hij (hlam e).symm)
    have h2 : W i j * (lam j - lam i) = 0 := by rw [mul_sub, h1]; ring
    exact (mul_eq_zero.1 h2).resolve_right hne

theorem exists_eigenbasis {F : Type*} [Field F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (lam : Fin n → F)
    (hlam : Function.Injective lam) (hroot : ∀ j, A.charpoly.IsRoot (lam j)) :
    ∃ U : Matrix (Fin n) (Fin n) F, IsUnit U.det ∧ A * U = U * diagonal lam := by
  have hev : ∀ j, Module.End.HasEigenvalue (Matrix.toLin' A) (lam j) := fun j =>
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by rw [Matrix.charpoly_toLin']; exact hroot j)
  choose u hu using fun j => (hev j).exists_hasEigenvector
  have hli : LinearIndependent F u := Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) lam hlam u hu
  refine ⟨Matrix.of fun i j => u j i, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  · ext i j
    have h1 := congrFun ((hu j).apply_eq_smul) i
    rw [Matrix.toLin'_apply] at h1
    rw [mul_diagonal]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1, mul_comm]

theorem exists_valHom_bounded_ker (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hL : FiniteDimensional ℚ_[p] L) (n : ℕ) (N : GL (Fin n) L) (hsep : N.val.charpoly.Separable) :
    ∃ (v : Subgroup.centralizer {N} →* Multiplicative (Fin n → ℤ)) (c : ℝ),
      ∀ z : Subgroup.centralizer {N}, v z = 1 → ∀ i j,
        ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c := by
  set φ : L →+* PadicAlgCl p := algebraMap L (PadicAlgCl p) with hφ
  set χ := N.val.charpoly with hχ
  have hsep' : (χ.map φ).Separable := hsep.map
  set s : Finset (PadicAlgCl p) := (χ.map φ).roots.toFinset with hs_def
  have hs : s.card = n := by
    rw [hs_def, Multiset.toFinset_card_of_nodup (nodup_roots hsep'), IsAlgClosed.card_roots_eq_natDegree,
      natDegree_map, hχ, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  set E : IntermediateField ℚ_[p] (PadicAlgCl p) :=
    L ⊔ IntermediateField.adjoin ℚ_[p] (s : Set (PadicAlgCl p)) with hE_def
  have hE : FiniteDimensional ℚ_[p] E := by
    have : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (s : Set (PadicAlgCl p))) :=
      IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
    infer_instance
  have hLE : L ≤ E := le_sup_left
  set ι : L →+* E := (IntermediateField.inclusion hLE).toRingHom with hι
  have hιφ : ((E.val : E →ₐ[ℚ_[p]] PadicAlgCl p) : E →+* PadicAlgCl p).comp ι = φ := by
    ext x; rfl
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hs)).symm
  have hmem : ∀ j, ((e j : PadicAlgCl p)) ∈ E := fun j =>
    (le_sup_right : IntermediateField.adjoin ℚ_[p] (s : Set (PadicAlgCl p)) ≤ E)
      (IntermediateField.subset_adjoin _ _ (e j).2)
  let lam : Fin n → E := fun j => ⟨e j, hmem j⟩
  have hlam : Function.Injective lam := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact e.injective (Subtype.ext h1)
  set A : Matrix (Fin n) (Fin n) E := N.val.map ι with hA
  have hroot : ∀ j, A.charpoly.IsRoot (lam j) := by
    intro j
    have h1 : (χ.map φ).IsRoot (e j : PadicAlgCl p) := by
      have h2 : ((e j : s) : PadicAlgCl p) ∈ (χ.map φ).roots.toFinset := (e j).2
      rw [Multiset.mem_toFinset] at h2
      exact (mem_roots hsep'.ne_zero).1 h2
    rw [hA, Matrix.charpoly_map, IsRoot.def]
    apply Subtype.val_injective
    have h3 : (((χ.map ι).eval (lam j) : E) : PadicAlgCl p) =
        ((E.val : E →ₐ[ℚ_[p]] PadicAlgCl p) : E →+* PadicAlgCl p) ((χ.map ι).eval (lam j)) := rfl
    rw [h3, eval_map, hom_eval₂, hιφ, ← eval_map]
    exact h1
  obtain ⟨U, hU, hAU⟩ := exists_eigenbasis A lam hlam hroot
  have hD : diagonal lam = U⁻¹ * A * U := by
    rw [Matrix.mul_assoc, hAU, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]

  let W : Subgroup.centralizer {N} → Matrix (Fin n) (Fin n) E :=
    fun z => U⁻¹ * ((z : GL (Fin n) L).val.map ι) * U
  have hcomm : ∀ z : Subgroup.centralizer {N},
      ((z : GL (Fin n) L).val.map ι) * A = A * ((z : GL (Fin n) L).val.map ι) := by
    intro z
    have h1 := Subgroup.mem_centralizer_iff.1 z.2 N (Set.mem_singleton N)
    have h2 : N.val * (z : GL (Fin n) L).val = (z : GL (Fin n) L).val * N.val := by
      rw [← Units.val_mul, ← Units.val_mul, h1]
    rw [hA, ← Matrix.map_mul, ← Matrix.map_mul, h2]
  have hdiag : ∀ z, W z = diagonal (fun i => W z i i) := by
    intro z
    apply eq_diagonal_of_commute lam hlam
    rw [hD]
    simp only [W, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hU, Matrix.mul_nonsing_inv_cancel_left _ _ hU,
      ← Matrix.mul_assoc _ A U, hcomm z, Matrix.mul_assoc]
  have hW1 : W 1 = 1 := by
    simp only [W, OneMemClass.coe_one, Units.val_one]
    rw [Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.mul_one, Matrix.nonsing_inv_mul _ hU]
  have hWmul : ∀ z w, W (z * w) = W z * W w := by
    intro z w
    have h1 : ((z * w : Subgroup.centralizer {N}) : GL (Fin n) L).val =
        (z : GL (Fin n) L).val * (w : GL (Fin n) L).val := rfl
    show U⁻¹ * (((z * w : Subgroup.centralizer {N}) : GL (Fin n) L).val.map ι) * U =
      (U⁻¹ * ((z : GL (Fin n) L).val.map ι) * U) * (U⁻¹ * ((w : GL (Fin n) L).val.map ι) * U)
    rw [h1, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hU]
  let μ : Fin n → (Subgroup.centralizer {N} →* E) := fun j =>
    { toFun := fun z => W z j j
      map_one' := by simp only [hW1, Matrix.one_apply_eq]
      map_mul' := fun z w => by
        show W (z * w) j j = W z j j * W w j j
        rw [hWmul]
        conv_lhs => rw [hdiag z, hdiag w]
        rw [diagonal_mul_diagonal, diagonal_apply_eq] }
  let μu : Fin n → (Subgroup.centralizer {N} →* Eˣ) := fun j => (μ j).toHomUnits
  let v : Subgroup.centralizer {N} →* Multiplicative (Fin n → ℤ) :=
    { toFun := fun z => Multiplicative.ofAdd (fun j => vK p E (μu j z))
      map_one' := by
        simp only [map_one, vK_one]
        rfl
      map_mul' := fun z w => by
        simp only [map_mul, vK_mul]
        rfl }
  refine ⟨v, ∑ i, ∑ k, ∑ j, ‖((U i j : E) : PadicAlgCl p)‖ * ‖((U⁻¹ j k : E) : PadicAlgCl p)‖, ?_⟩
  intro z hz i k
  have hv0 : ∀ j, vK p E (μu j z) = 0 := by
    intro j
    have h1 : (fun j => vK p E (μu j z)) = 0 := ofAdd_eq_one.1 hz
    exact congrFun h1 j
  have hnorm : ∀ j, ‖((W z j j : E) : PadicAlgCl p)‖ = 1 := fun j =>
    (mem_UK_iff p E hE (μu j z)).2 (hv0 j)
  have hz' : (z : GL (Fin n) L).val.map ι = U * diagonal (fun j => W z j j) * U⁻¹ := by
    rw [← hdiag z]
    simp only [W, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hU, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hU]
  have hent : ((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i k : L) : PadicAlgCl p) =
      ((((z : GL (Fin n) L).val.map ι) i k : E) : PadicAlgCl p) := rfl
  rw [hent, hz']
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, IntermediateField.coe_sum, IntermediateField.coe_mul]
  calc _ ≤ ∑ j, ‖((U i j : E) : PadicAlgCl p) * ((W z j j : E) : PadicAlgCl p) *
          ((U⁻¹ j k : E) : PadicAlgCl p)‖ := norm_sum_le _ _
    _ = ∑ j, ‖((U i j : E) : PadicAlgCl p)‖ * ‖((U⁻¹ j k : E) : PadicAlgCl p)‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_mul, norm_mul, hnorm j, mul_one]
    _ ≤ ∑ k', ∑ j, ‖((U i j : E) : PadicAlgCl p)‖ * ‖((U⁻¹ j k' : E) : PadicAlgCl p)‖ :=
        Finset.single_le_sum (f := fun k' => ∑ j, ‖((U i j : E) : PadicAlgCl p)‖ *
          ‖((U⁻¹ j k' : E) : PadicAlgCl p)‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (Finset.mem_univ k)
    _ ≤ _ :=
        Finset.single_le_sum (f := fun i' => ∑ k', ∑ j, ‖((U i' j : E) : PadicAlgCl p)‖ *
          ‖((U⁻¹ j k' : E) : PadicAlgCl p)‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (Finset.mem_univ i)

theorem centralizer_valHom_bounded_ker : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] L →
    ∀ (n : ℕ) (N : GL (Fin n) L), N.val.charpoly.Separable →
    ∃ (v : Subgroup.centralizer {N} →* Multiplicative (Fin n → ℤ)) (c : ℝ),
      ∀ z : Subgroup.centralizer {N}, v z = 1 → ∀ i j,
        ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c :=
  fun p _ L hL n N hsep => exists_valHom_bounded_ker p L hL n N hsep

end GlobalTheory.CentValHom
end
end

section
open Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_bounded_valuation_kernel : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] L →
    ∀ (n : ℕ) (N : GL (Fin n) L), N.val.charpoly.Separable →
    ∃ (v : Subgroup.centralizer {N} →* Multiplicative (Fin n → ℤ)) (c : ℝ),
      ∀ z : Subgroup.centralizer {N}, v z = 1 → ∀ i j,
        ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c := by
  first | (exact @GlobalTheory.CentValHom.centralizer_valHom_bounded_ker) | (exact GlobalTheory.CentValHom.centralizer_valHom_bounded_ker) | (intros; apply GlobalTheory.CentValHom.centralizer_valHom_bounded_ker  <;> assumption)
end

section
open Matrix
open scoped Classical

namespace GlobalTheory.LKLoc

theorem inv_mul_entry_mem_intK (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ)
    (a b : GL (Fin n) L) (C ε : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i j, ‖((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j‖ ≤ C)
    (hab : ∀ i j, ‖(b : Matrix (Fin n) (Fin n) L) i j - (a : Matrix (Fin n) (Fin n) L) i j‖ ≤ ε)
    (hε : n * C * ε ≤ 1) (i j : Fin n) :
    ((a⁻¹ * b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intK p L := by
  have key : ((a⁻¹ * b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      1 + ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((b : Matrix (Fin n) (Fin n) L) - (a : Matrix (Fin n) (Fin n) L)) := by
    rw [Units.val_mul, Matrix.mul_sub, Units.inv_mul]
    abel
  have hs : ‖(((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((b : Matrix (Fin n) (Fin n) L) - (a : Matrix (Fin n) (Fin n) L))) i j‖ ≤ 1 := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i k *
            ((b : Matrix (Fin n) (Fin n) L) - (a : Matrix (Fin n) (Fin n) L)) k j‖
        ≤ ∑ _k : Fin n, C * ε := Finset.sum_le_sum fun k _ => by
          rw [norm_mul]
          exact mul_le_mul (ha i k) (by simpa using hab k j) (norm_nonneg _) hC
      _ = n * C * ε := by simp [mul_assoc]
      _ ≤ 1 := hε
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  change ‖(( ((a⁻¹ * b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ 1
  rw [key, Matrix.add_apply, IntermediateField.coe_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 hs)

theorem exists_finset_inv_mul_mem_KintK : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] L →
    ∀ (n : ℕ) (B : Subgroup (GL (Fin n) L)) (c : ℝ),
      (∀ z ∈ B, ∀ i j, ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c) →
      ∃ T : Finset (GL (Fin n) L), (∀ t ∈ T, t ∈ B) ∧ ∀ z ∈ B, ∃ t ∈ T, t⁻¹ * z ∈ GlobalTheory.LKLoc.KintK p L n := by
  intro p _ L hL n B c hB
  haveI : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  set C := max c 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  set ε : ℝ := 1 / (2 * (n * C + 1)) with hεdef
  have hε : 0 < ε := by positivity
  let f : GL (Fin n) L → (Fin n → Fin n → L) := fun z i j => (z : Matrix (Fin n) (Fin n) L) i j
  let S : Set (Fin n → Fin n → L) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : L) C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.1 hS.totallyBounded ε hε
  let g : (Fin n → Fin n → L) → GL (Fin n) L := fun y =>
    if h : ∃ z ∈ B, dist (f z) y < ε then h.choose else 1
  have hgB : ∀ y, g y ∈ B := fun y => by
    by_cases h : ∃ z ∈ B, dist (f z) y < ε
    · simp only [g, dif_pos h]; exact h.choose_spec.1
    · simp only [g, dif_neg h]; exact B.one_mem
  have hbd : ∀ z ∈ B, ∀ i j, ‖(z : Matrix (Fin n) (Fin n) L) i j‖ ≤ C := fun z hz i j =>
    (hB z hz i j).trans (le_max_left _ _)
  have hnC : (n : ℝ) * C * (2 * ε) ≤ 1 := by
    rw [hεdef]
    have h0 : (0 : ℝ) < n * C + 1 := by positivity
    rw [show (n : ℝ) * C * (2 * (1 / (2 * (n * C + 1)))) = n * C / (n * C + 1) by field_simp]
    rw [div_le_one h0]; linarith
  refine ⟨ht.toFinset.image g, ?_, ?_⟩
  · intro s hs
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hs
    exact hgB y
  · intro z hz
    have hzS : f z ∈ S := by
      simp only [S, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
      intro i j; exact hbd z hz i j
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (hcov hzS)
    have hex : ∃ z ∈ B, dist (f z) y < ε := ⟨z, hz, hzy⟩
    have hgy : g y ∈ B ∧ dist (f (g y)) y < ε := by
      simp only [g, dif_pos hex]; exact hex.choose_spec
    refine ⟨g y, Finset.mem_image.2 ⟨y, ht.mem_toFinset.2 hy, rfl⟩, ?_⟩
    obtain ⟨hwB, hwy⟩ := hgy
    set w := g y
    have hd : dist (f z) (f w) ≤ 2 * ε := by
      have := dist_triangle_right (f z) (f w) y
      have := Metric.mem_ball.1 hzy
      linarith
    have hent : ∀ i j, ‖(z : Matrix (Fin n) (Fin n) L) i j - (w : Matrix (Fin n) (Fin n) L) i j‖ ≤ 2 * ε :=
      fun i j => by
        rw [← dist_eq_norm]
        exact ((dist_le_pi_dist (f z i) (f w i) j).trans (dist_le_pi_dist (f z) (f w) i)).trans hd
    rw [KintK, GlobalTheory.LKRes.mem_range_map_subtype_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact inv_mul_entry_mem_intK p L n w z C (2 * ε) hC (hbd _ (B.inv_mem hwB)) hent hnC i j
    · rw [_root_.mul_inv_rev, inv_inv]
      exact inv_mul_entry_mem_intK p L n z w C (2 * ε) hC (hbd _ (B.inv_mem hz))
        (fun i j => by rw [norm_sub_rev]; exact hent i j) hnC i j

end GlobalTheory.LKLoc
end

section
open Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_subgroup_finite_cosets : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] L →
    ∀ (n : ℕ) (B : Subgroup (GL (Fin n) L)) (c : ℝ),
      (∀ z ∈ B, ∀ i j, ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c) →
      ∃ T : Finset (GL (Fin n) L), (∀ t ∈ T, t ∈ B) ∧ ∀ z ∈ B, ∃ t ∈ T, t⁻¹ * z ∈ GlobalTheory.LKLoc.KintK p L n := by
  first | (exact @GlobalTheory.LKLoc.exists_finset_inv_mul_mem_KintK) | (exact GlobalTheory.LKLoc.exists_finset_inv_mul_mem_KintK) | (intros; apply GlobalTheory.LKLoc.exists_finset_inv_mul_mem_KintK <;> assumption)
end

section
open Matrix
open scoped Classical

namespace GlobalTheory.CentProd

open GlobalTheory.LKRes

noncomputable def incl {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (i : Fin (d + 1)) : GL (Fin n) S →* GL (Fin n) R :=
  (glPiEquiv d n e).symm.toMonoidHom.comp (MonoidHom.mulSingle (fun _ => GL (Fin n) S) i)

theorem glPiEquiv_incl {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (i : Fin (d + 1)) (g : GL (Fin n) S) : glPiEquiv d n e (incl d n e i g) = Pi.mulSingle i g := by
  simp [incl]

theorem mem_centralizer_iff_comp {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (N z : GL (Fin n) R) :
    z ∈ Subgroup.centralizer {N} ↔ ∀ i, glPiEquiv d n e z i ∈ Subgroup.centralizer {glPiEquiv d n e N i} := by
  simp only [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h i
    have := congrArg (fun x => glPiEquiv d n e x i) h
    simpa [map_mul] using this
  · intro h
    apply (glPiEquiv d n e).injective
    funext i
    simpa [map_mul] using h i

theorem charpoly_comp {R S : Type} [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (N : GL (Fin n) R) (i : Fin (d + 1)) :
    (glPiEquiv d n e N i).val.charpoly = N.val.charpoly.map ((Pi.evalRingHom (fun _ => S) i).comp (e : R →+* _)) := by
  have h : (glPiEquiv d n e N i).val = ((Pi.evalRingHom (fun _ => S) i).comp (e : R →+* _)).mapMatrix N.val := by
    ext a b
    rfl
  rw [h, RingHom.mapMatrix_apply, Matrix.charpoly_map]

theorem centralizer_fg_of_pi : ∀ (R S : Type) [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (A : Subring R) (B : Subring S), (∀ x : R, x ∈ A ↔ ∀ i, e x i ∈ B) →
    (∀ N : GL (Fin n) S, N.val.charpoly.Separable → ∃ G : Finset (GL (Fin n) S),
      (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) S)) ∪
        ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) B.subtype).range : Subgroup _) :
          Set (GL (Fin n) S)))) →
    ∀ N : GL (Fin n) R, N.val.charpoly.Separable → ∃ G : Finset (GL (Fin n) R),
      (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) R)) ∪
        ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) A.subtype).range : Subgroup _) :
          Set (GL (Fin n) R))) := by
  intro R S _ _ d n e A B hAB hS N hN
  set ψ := glPiEquiv d n e with hψ
  have hNi : ∀ i, (ψ N i).val.charpoly.Separable := fun i => by
    rw [hψ, charpoly_comp]; exact hN.map
  choose Gs hGs1 hGs2 using fun i => hS (ψ N i) (hNi i)

  have hinclC : ∀ i g, g ∈ Subgroup.centralizer {ψ N i} → incl d n e i g ∈ Subgroup.centralizer {N} := by
    intro i g hg
    rw [mem_centralizer_iff_comp d n e]
    intro j
    rw [glPiEquiv_incl]
    by_cases hij : j = i
    · subst hij; simpa using hg
    · rw [Pi.mulSingle_eq_of_ne hij]; exact one_mem _
  have hinclA : ∀ i g, g ∈ (GeneralLinearGroup.map (n := Fin n) B.subtype).range →
      incl d n e i g ∈ (GeneralLinearGroup.map (n := Fin n) A.subtype).range := by
    intro i g hg
    rw [glPiEquiv_mem_iff d n e A B hAB]
    intro j
    rw [glPiEquiv_incl]
    by_cases hij : j = i
    · subst hij; simpa using hg
    · rw [Pi.mulSingle_eq_of_ne hij]; exact one_mem _
  refine ⟨Finset.univ.biUnion (fun i => (Gs i).image (incl d n e i)), ?_, ?_⟩
  · intro g hg
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hg
    obtain ⟨i, g', hg', rfl⟩ := hg
    exact hinclC i g' (hGs1 i g' hg')
  · intro z hz
    set K := Subgroup.closure (((Finset.univ.biUnion (fun i => (Gs i).image (incl d n e i)) : Finset _) :
      Set (GL (Fin n) R)) ∪
        ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) A.subtype).range : Subgroup _) :
          Set (GL (Fin n) R))) with hK
    have hpi : ψ z ∈ Subgroup.pi Set.univ (fun i => Subgroup.closure (((Gs i : Set (GL (Fin n) S))) ∪
        ((Subgroup.centralizer {ψ N i} ⊓ (GeneralLinearGroup.map (n := Fin n) B.subtype).range : Subgroup _) :
          Set (GL (Fin n) S)))) := by
      intro i _
      exact hGs2 i ((mem_centralizer_iff_comp d n e N z).1 hz i)
    have hle : Subgroup.pi Set.univ (fun i => Subgroup.closure (((Gs i : Set (GL (Fin n) S))) ∪
        ((Subgroup.centralizer {ψ N i} ⊓ (GeneralLinearGroup.map (n := Fin n) B.subtype).range : Subgroup _) :
          Set (GL (Fin n) S)))) ≤ K.map ψ.toMonoidHom := by
      rw [Subgroup.pi_le_iff]
      intro i
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_map_equiv]
      have : (MonoidHom.mulSingle (fun _ => GL (Fin n) S) i) g = ψ (incl d n e i g) := by
        rw [hψ, glPiEquiv_incl]; rfl
      rw [this, MulEquiv.symm_apply_apply]
      apply Subgroup.subset_closure
      rcases hg with hg | hg
      · left
        simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
          Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨i, g, hg, rfl⟩
      · right
        exact ⟨hinclC i g hg.1, hinclA i g hg.2⟩
    have := hle hpi
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at this
    exact this

end GlobalTheory.CentProd
end

section
open Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_finite_generation_transfer : ∀ (R S : Type) [CommRing R] [CommRing S] (d n : ℕ) (e : R ≃+* (Fin (d + 1) → S))
    (A : Subring R) (B : Subring S), (∀ x : R, x ∈ A ↔ ∀ i, e x i ∈ B) →
    (∀ N : GL (Fin n) S, N.val.charpoly.Separable → ∃ G : Finset (GL (Fin n) S),
      (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) S)) ∪
        ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) B.subtype).range : Subgroup _) :
          Set (GL (Fin n) S)))) →
    ∀ N : GL (Fin n) R, N.val.charpoly.Separable → ∃ G : Finset (GL (Fin n) R),
      (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) R)) ∪
        ((Subgroup.centralizer {N} ⊓ (GeneralLinearGroup.map (n := Fin n) A.subtype).range : Subgroup _) :
          Set (GL (Fin n) R))) := by
  first | (exact @GlobalTheory.CentProd.centralizer_fg_of_pi) | (exact GlobalTheory.CentProd.centralizer_fg_of_pi) | (intros; apply GlobalTheory.CentProd.centralizer_fg_of_pi  <;> assumption)
end

section
noncomputable section

open Matrix GlobalTheory.LKRes ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct Classical

namespace GlobalTheory.CentFG

theorem field_case (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hL : FiniteDimensional ℚ_[p] L) (n : ℕ) (N : GL (Fin n) L) (hN : N.val.charpoly.Separable) :
    ∃ G : Finset (GL (Fin n) L), (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) L)) ∪
        ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKLoc.KintK p L n : Subgroup _) : Set (GL (Fin n) L))) := by
  obtain ⟨v, c, hv⟩ := GlobalTheory.T.centralizer_bounded_valuation_kernel p L hL n N hN
  have hfg : v.range.FG := by
    rw [Subgroup.fg_iff_add_fg]
    exact (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule v.range.toAddSubgroup)).1
      (IsNoetherian.noetherian (R := ℤ) (M := Additive (Multiplicative (Fin n → ℤ))) _)
  obtain ⟨S, hS⟩ := hfg
  have hpre : ∀ s : S, ∃ z : Subgroup.centralizer {N}, v z = s := fun s =>
    (show (s : Multiplicative (Fin n → ℤ)) ∈ v.range from hS ▸ Subgroup.subset_closure s.2)
  choose pre hpre using hpre
  let B : Subgroup (GL (Fin n) L) := v.ker.map (Subgroup.centralizer {N}).subtype
  obtain ⟨T, hT, hTB⟩ := GlobalTheory.T.bounded_subgroup_finite_cosets p L hL n B c (by
    rintro _ ⟨z, hz, rfl⟩ i j
    exact hv z hz i j)
  refine ⟨Finset.univ.image (fun s => ((pre s : Subgroup.centralizer {N}) : GL (Fin n) L)) ∪ T, ?_, ?_⟩
  · intro g hg
    rcases Finset.mem_union.1 hg with h | h
    · obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 h
      exact (pre s).2
    · obtain ⟨z, -, rfl⟩ := hT g h
      exact z.2
  · intro z hz
    set C := Subgroup.closure (((Finset.univ.image (fun s => ((pre s : Subgroup.centralizer {N}) : GL (Fin n) L)) ∪ T :
      Finset _) : Set (GL (Fin n) L)) ∪ ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKLoc.KintK p L n : Subgroup _) : Set (GL (Fin n) L)))
    let W : Subgroup (Subgroup.centralizer {N}) := Subgroup.closure (Set.range pre)
    have hW : W.map v = v.range := by
      rw [MonoidHom.map_closure, ← hS]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        rw [hpre]; exact s.2
      · intro hx
        exact ⟨pre ⟨x, hx⟩, ⟨_, rfl⟩, hpre _⟩
    obtain ⟨w, hw, hwv⟩ : v ⟨z, hz⟩ ∈ W.map v := by rw [hW]; exact ⟨_, rfl⟩
    have hWle : W ≤ C.comap (Subgroup.centralizer {N}).subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨s, rfl⟩
      refine Subgroup.subset_closure (Or.inl ?_)
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_union,
        Set.mem_range]
      exact Or.inl ⟨s, rfl⟩
    have hWC : ∀ y ∈ W, (y : GL (Fin n) L) ∈ C := fun y hy => hWle hy
    have hk : w⁻¹ * ⟨z, hz⟩ ∈ v.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwv, inv_mul_cancel]
    obtain ⟨t, htT, ht⟩ := hTB _ ⟨_, hk, rfl⟩
    have htZ : t ∈ Subgroup.centralizer {N} := by
      obtain ⟨y, -, rfl⟩ := hT t htT; exact y.2
    have hrest : t⁻¹ * ((w : GL (Fin n) L)⁻¹ * z) ∈ C := by
      refine Subgroup.subset_closure (Or.inr ⟨?_, ?_⟩)
      · exact (Subgroup.centralizer {N}).mul_mem ((Subgroup.centralizer {N}).inv_mem htZ)
          ((Subgroup.centralizer {N}).mul_mem ((Subgroup.centralizer {N}).inv_mem w.2) hz)
      · simpa using ht
    have htC : t ∈ C := Subgroup.subset_closure (Or.inl (by simp [htT]))
    have : z = (w : GL (Fin n) L) * t * (t⁻¹ * ((w : GL (Fin n) L)⁻¹ * z)) := by group
    rw [this]
    exact C.mul_mem (C.mul_mem (hWC w hw) htC) hrest

theorem centralizer_le_closure : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K →
    ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∃ G : Finset (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)), (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r))) ∪
        ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKRes.Kres p K n r : Subgroup _) : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)))) := by
  intro p _ K hK n r hr N hN
  obtain ⟨f, -, hf⟩ := qK_eq_pow p K hK
  obtain ⟨e, -, -, -, -, -, -, hint⟩ := GlobalTheory.T.unramified_extension_product_decomposition p K hK f r hf hr
  have hd : 0 < Nat.gcd f r := Nat.gcd_pos_of_pos_right _ hr
  have hfin : FiniteDimensional ℚ_[p] (Kn p K (r / Nat.gcd f r)) :=
    finiteDimensional_Kn p K hK (Nat.div_pos (Nat.gcd_le_right _ hr) hd)
  generalize Nat.gcd f r = g at *
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  exact GlobalTheory.T.centralizer_finite_generation_transfer _ _ k n e (intKQ p K r) (GlobalTheory.LKLoc.intR p K (r / (k + 1))) hint
    (fun N' hN' => field_case p _ hfin n N' hN') N hN

end GlobalTheory.CentFG
end
end

section
open Matrix GlobalTheory.LKRes
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_finitely_generated_mod_open : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∃ G : Finset (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)), (∀ g ∈ G, g ∈ Subgroup.centralizer {N}) ∧
      Subgroup.centralizer {N} ≤ Subgroup.closure ((G : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r))) ∪
        ((Subgroup.centralizer {N} ⊓ GlobalTheory.LKRes.Kres p K n r : Subgroup _) : Set (GL (Fin n) (GlobalTheory.LKRes.KQ p K r)))) := by
  first | (exact @GlobalTheory.CentFG.centralizer_le_closure) | (exact GlobalTheory.CentFG.centralizer_le_closure) | (intros; apply GlobalTheory.CentFG.centralizer_le_closure <;> assumption)
end
