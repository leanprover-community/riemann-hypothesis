import Formalism.WachLatticeTwists.RamifiedBlockRings.RightIdealImageOfSurjective
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalModuleOf

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem resConst : StatResConst := by
  unfold StatResConst
  intro O _ _ X T hT f hf x y
  set g : T := ⟨f, hf⟩ - algebraMap O T (f x) with hg
  have hgnu : ¬ IsUnit g := by
    intro hu
    have := hu.map ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom)
    simp [hg] at this
  let ψ : T →+* IsLocalRing.ResidueField O :=
    (IsLocalRing.residue O).comp ((Pi.evalRingHom (fun _ : X => O) y).comp T.val.toRingHom)
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective z
    exact ⟨algebraMap O T c, by simp [ψ]⟩
  have hmax : (RingHom.ker ψ).IsMaximal := RingHom.ker_isMaximal_of_surjective ψ hsurj
  have hker : RingHom.ker ψ = IsLocalRing.maximalIdeal T := IsLocalRing.eq_maximalIdeal hmax
  have hgm : g ∈ RingHom.ker ψ := by
    rw [hker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hgnu
  rw [RingHom.mem_ker] at hgm
  simp [ψ, hg, sub_eq_zero] at hgm
  exact hgm.symm

theorem sepPoint : StatSepPoint := by
  unfold StatSepPoint
  intro O _ _ X _ T hsep x
  classical
  have hy : ∀ y, ∃ g ∈ T, y ≠ x → g y = 0 ∧ g x ≠ 0 := by
    intro y
    by_cases hyx : y = x
    · exact ⟨1, T.one_mem, fun h => absurd hyx h⟩
    · obtain ⟨f, hf, hne⟩ := hsep x y (Ne.symm hyx)
      refine ⟨f - algebraMap O (X → O) (f y), T.sub_mem hf (T.algebraMap_mem _), fun _ => ⟨by simp, ?_⟩⟩
      simpa [sub_eq_zero] using hne
  choose g hgT hg using hy
  refine ⟨∏ y ∈ Finset.univ.erase x, g y, prod_mem fun y _ => hgT y, ?_, ?_⟩
  · rw [Finset.prod_apply, Finset.prod_ne_zero_iff]
    intro y hy
    exact (hg y (Finset.ne_of_mem_erase hy)).2
  · intro z hz
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hz, Finset.mem_univ z⟩) (hg z hz).1

theorem satur : DvrArtinReesInclusion := by
  unfold DvrArtinReesInclusion
  intro O _ _ _ M _ _ _ _ R
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (IsLocalRing.maximalIdeal O) R
  refine ⟨k + 1, fun a ha haN => ?_⟩
  have hmem : a ∈ (IsLocalRing.maximalIdeal O) ^ (k + 1) • (⊤ : Submodule O M) ⊓ R :=
    Submodule.mem_inf.2 ⟨haN, ha⟩
  rw [hk (k + 1) (Nat.le_succ k), Nat.add_sub_cancel_left, pow_one] at hmem
  exact Submodule.smul_mono le_rfl inf_le_right hmem

theorem idemSmall : StatIdemSmall := by
  unfold StatIdemSmall
  intro O _ _ _ n _ _ e he h0
  have h1 : (IsLocalRing.residue O).mapMatrix (1 - e) = 1 := by
    rw [map_sub, map_one, RingHom.mapMatrix_apply, h0, sub_zero]
  have hres : IsLocalRing.residue O (1 - e).det = 1 := by
    rw [RingHom.map_det, h1, Matrix.det_one]
  have hdet : IsUnit (1 - e).det := by
    by_contra hnu
    have hm : (1 - e).det ∈ IsLocalRing.maximalIdeal O := hnu
    rw [← IsLocalRing.residue_eq_zero_iff] at hm
    rw [hm] at hres
    exact zero_ne_one hres
  have hmul : e * (1 - e) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, he, sub_self]
  calc e = e * (1 - e) * (1 - e)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    _ = 0 := by rw [hmul, Matrix.zero_mul]



theorem rootsInt : StatRootsInt := by
  unfold StatRootsInt
  intro O _ _ _ P t α hP
  have hinj : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  have hmon : (P.map (algebraMap O (FractionRing O))).Monic := by
    rw [hP]
    exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hPm : P.Monic := by
    first
    | exact Polynomial.monic_of_injective hinj hmon
    | (rw [Polynomial.Monic, ← hinj.eq_iff, map_one, ← Polynomial.leadingCoeff_map_of_injective hinj]
       exact hmon)
  have hint : ∀ i, ∃ b : O, algebraMap O (FractionRing O) b = α i := by
    intro i
    have hroot : Polynomial.eval₂ (algebraMap O (FractionRing O)) (α i) P = 0 := by
      rw [Polynomial.eval₂_eq_eval_map, hP, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    exact IsIntegrallyClosed.isIntegral_iff.1 ⟨P, hPm, hroot⟩
  choose β hβ using hint
  refine ⟨β, hβ, ?_⟩
  apply Polynomial.map_injective _ hinj
  rw [hP, Polynomial.map_prod]
  simp [hβ]

theorem lemma_five_three_holds : BlockRingDecompositionLemma := by
  unfold BlockRingDecompositionLemma
  intro O _ _ _ X d G _ _ _ t ht bl T D _ _ hTop Z NN _ _ g₀ n hspan hZ hcard
  unfold RingData.Top RingTop at hTop
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, h9, h10, -⟩ := hTop

  have hsum : ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} = Fintype.card d := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv bl)
  have hcard' : ((g₀ * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
      Cardinal.mk (IsLocalRing.ResidueField O) := by
    rw [hsum]; exact hcard

  have hmain := Formalism.NG.globalModule O X D.X' T D.T' Z D.p D.q D.b h1 (fun x _ => h2 x) d D.R' h3
    NN g₀ n hspan hZ D.π' D.ρπ h7 (Fin (t + 1)) bl h8 D.ρk h9 h10 hcard'
  exact hmain.trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _))

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem cornerIdem : CornerIdempotentInSubalgebra := by
  unfold CornerIdempotentInSubalgebra
  intro k _ n ι _ _ B hn hsurj A
  classical
  obtain ⟨p, q, hpq⟩ : ∃ p q : n, p ≠ q := Fintype.exists_pair_of_one_lt_card hn
  have hc : ((Matrix.single p p (1 : k) - Matrix.single q q 1 : Matrix n n k), (0 : ι → k)) ∈ B := by
    obtain ⟨z1, hz1B, hz1⟩ := hsurj (Matrix.single p q 1)
    obtain ⟨z2, hz2B, hz2⟩ := hsurj (Matrix.single q p 1)
    have := B.sub_mem (B.mul_mem hz1B hz2B) (B.mul_mem hz2B hz1B)
    convert this using 1
    refine Prod.ext ?_ ?_
    · simp [hz1, hz2, Matrix.single_mul_single_same]
    · simp [mul_comm]
  have hij : ∀ i j, ((Matrix.single i j (1 : k) : Matrix n n k), (0 : ι → k)) ∈ B := by
    intro i j
    obtain ⟨w1, hw1B, hw1⟩ := hsurj (Matrix.single i p 1)
    obtain ⟨w2, hw2B, hw2⟩ := hsurj (Matrix.single p j 1)
    have := B.mul_mem (B.mul_mem hw1B hc) hw2B
    convert this using 1
    refine Prod.ext ?_ ?_
    · simp [hw1, hw2, Matrix.mul_sub, Matrix.sub_mul, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne, hpq]
    · simp
  have hA : (A, (0 : ι → k)) = ∑ i, ∑ j, A i j • ((Matrix.single i j (1 : k) : Matrix n n k), (0 : ι → k)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sum, Prod.smul_fst, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single A
    · simp [Prod.snd_sum]
  rw [hA]
  exact B.sum_mem fun i _ => B.sum_mem fun j _ => B.smul_mem (hij i j) _

theorem charpolyRev_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {d : Type*} [Fintype d]
    [DecidableEq d] (M : Matrix d d A) :
    (Matrix.charpolyRev M).map f = Matrix.charpolyRev (M.map f) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem nilConst : StatNilConst := by
  intro O _ _ X T d _ _ hT a ha y hy x
  have hrev : Matrix.charpolyRev ((a x).map (IsLocalRing.residue O)) = 1 := by
    have h1 : Matrix.charpolyRev ((a x).map (IsLocalRing.residue O)) =
        Matrix.charpolyRev ((a y).map (IsLocalRing.residue O)) := by
      rw [← charpolyRev_map, ← charpolyRev_map]
      ext k
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      exact resConst O X T hT _ (ha k) x y
    rw [h1, hy]
    simp [Matrix.charpolyRev]
  set M := (a x).map (IsLocalRing.residue O) with hM
  have hcp : M.charpoly = Polynomial.X ^ Fintype.card d := by
    have hdeg : M.charpoly.natDegree = Fintype.card d := Matrix.charpoly_natDegree_eq_dim M
    ext k
    rw [Polynomial.coeff_X_pow]
    by_cases hk : k ≤ Fintype.card d
    · have h2 : M.charpoly.reverse.coeff (Fintype.card d - k) = M.charpoly.coeff k := by
        rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_le (Nat.sub_le _ _)]
        congr 1; omega
      rw [← h2, Matrix.reverse_charpoly, hrev, Polynomial.coeff_one]
      by_cases hk2 : k = Fintype.card d
      · simp [hk2]
      · rw [if_neg (by omega), if_neg hk2]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), if_neg (by omega)]
  have hch := Matrix.aeval_self_charpoly M
  rw [hcp] at hch
  have h5 : ((a x) ^ Fintype.card d).map (IsLocalRing.residue O) = M ^ Fintype.card d := by
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
  rw [h5]
  simpa using hch

theorem tailProd {M : Type*} [CommMonoid M] (f : ℕ → M) (t : ℕ) :
    ((List.range t).tail.map f).prod = ∏ i ∈ Finset.Ioo 0 t, f i := by
  cases t with
  | zero => simp
  | succ n =>
    rw [List.range_succ_eq_map, List.tail_cons, List.map_map, ← List.prod_toFinset _ List.nodup_range,
      List.toFinset_range]
    have hI : Finset.Ioo 0 (n + 1) = (Finset.range n).map ⟨Nat.succ, Nat.succ_injective⟩ := by
      ext i
      simp only [Finset.mem_Ioo, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨i - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩
        omega
    (rw [hI, Finset.prod_map]) <;> rfl

theorem listDiag {A : Type*} [CommRing A] {d : Type*} [Fintype d] [DecidableEq d] (f : ℕ → d → A)
    (l : List ℕ) :
    (l.map fun i => (Matrix.diagonal (f i) : Matrix d d A)).prod =
      Matrix.diagonal fun a => (l.map fun i => f i a).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih, Matrix.diagonal_mul_diagonal]

theorem eDiag : StatEDiag := by
  unfold StatEDiag
  intro A _ d _ _ S β t α
  dsimp only
  have hfac : ∀ i, (Matrix.diagonal (fun a => if S a then β a else 0) -
      α i • Matrix.diagonal (fun a => if S a then (1 : A) else 0)) =
      Matrix.diagonal (fun a => if S a then β a - α i else 0) := by
    intro i
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hS : S a <;> simp [hS]
    · simp [Matrix.diagonal_apply_ne _ hab]
  simp_rw [hfac]
  rw [listDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases hS : S a
  · simp only [hS, ↓reduceIte, one_mul]
    exact tailProd _ t
  · simp [hS]

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end
