import ReciprocityTheory.SemistableReduction.SemiDegSt

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem exists_kBasisIn {K : Type} [Field K] [NumberField K] {r : ℕ}
    (B : Submodule (𝓞 K) (Fin r → K)) : ∃ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b := by
  classical
  obtain ⟨s, hsB, hspan, hli⟩ := exists_linearIndependent K (B : Set (Fin r → K))
  have hfin : s.Finite := by
    first
    | exact hli.setFinite
    | exact Set.toFinite s
    | exact (Set.finite_coe_iff.mp hli.finite)
  haveI : Fintype s := hfin.fintype
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => ((e.symm i : s) : Fin r → K), fun i => hsB (e.symm i).2,
    hli.comp _ e.symm.injective, ?_⟩
  intro x hx
  have hx' : x ∈ Submodule.span K s := by
    rw [hspan]
    exact Submodule.subset_span hx
  have hr : Set.range (fun i => ((e.symm i : s) : Fin r → K)) = s := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
  rw [hr]
  exact hx'

theorem kBasisIn_bot_eq {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (hb : IsKBasisIn (⊥ : Submodule (𝓞 K) (Fin r → K)) b) : k = 0 := by
  obtain ⟨hmem, hli, -⟩ := hb
  by_contra hk
  have i : Fin k := ⟨0, Nat.pos_of_ne_zero hk⟩
  exact hli.ne_zero i ((Submodule.mem_bot _).mp (hmem i))

theorem latDeg_zero_fam {K : Type} [Field K] [NumberField K] {r : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin 0 → Fin r → K) (hb : IsKBasisIn B b) : latDeg H B b = 0 := by
  obtain ⟨-, -, hspan⟩ := hb
  have hB : B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h := hspan x hx
    simpa [Set.range_eq_empty] using h
  subst hB
  simp [latDeg, Set.range_eq_empty]

theorem spanIdx_ne_zero {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (hB : B.FG)
    (hb : IsKBasisIn B b) : spanIdx B b ≠ 0 := by
  classical
  obtain ⟨hmem, hli, hspan⟩ := hb
  obtain ⟨G, hG⟩ := id hB
  have hcoef : ∀ g ∈ G, ∃ c : Fin k → K, g = ∑ i, c i • b i := by
    intro g hg
    have hgB : g ∈ B := by
      rw [← hG]
      exact Submodule.subset_span hg
    exact ((Submodule.mem_span_range_iff_exists_fun K).mp (hspan g hgB)).imp fun c hc => hc.symm
  choose! c hc using hcoef
  obtain ⟨β, hβ⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (𝓞 K)) (S := K)
    (G ×ˢ (Finset.univ : Finset (Fin k))) (fun p => c p.1 p.2)
  have hβS : ∀ x ∈ B, (β : 𝓞 K) • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro x hx
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      rw [hc g hg, Finset.smul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨t, ht⟩ := hβ (g, i) (Finset.mem_product.mpr ⟨hg, Finset.mem_univ _⟩)
      rw [← smul_assoc]
      simp only at ht
      rw [← ht, algebraMap_smul]
      exact Submodule.smul_mem _ t (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ a hx
  have hβ0 : (β : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero β
  have hint : IsIntegral ℤ (β : 𝓞 K) := Algebra.IsIntegral.isIntegral _
  have hp0 : (minpoly ℤ (β : 𝓞 K)).coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := minpoly ℤ (β : 𝓞 K))
    rw [h0, map_zero, sub_zero] at hq
    have hmon : q.Monic := Polynomial.monic_X.of_mul_monic_left (hq ▸ minpoly.monic hint)
    have hq0 : Polynomial.aeval (β : 𝓞 K) q = 0 := by
      have h := minpoly.aeval ℤ (β : 𝓞 K)
      rw [hq, map_mul, Polynomial.aeval_X] at h
      exact (mul_eq_zero.mp h).resolve_left hβ0
    have hdeg : (minpoly ℤ (β : 𝓞 K)).degree ≤ q.degree := by
      first
      | exact minpoly.min ℤ (β : 𝓞 K) hmon hq0
      | exact minpoly.min (A := ℤ) (x := (β : 𝓞 K)) hmon hq0
    rw [hq, Polynomial.degree_mul, Polynomial.degree_X,
      Polynomial.degree_eq_natDegree hmon.ne_zero] at hdeg
    have h2 : 1 + q.natDegree ≤ q.natDegree := by exact_mod_cast hdeg
    omega
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := minpoly ℤ (β : 𝓞 K))
  have hdiv : (((minpoly ℤ (β : 𝓞 K)).coeff 0 : ℤ) : 𝓞 K) =
      (β : 𝓞 K) * (-(Polynomial.aeval (β : 𝓞 K) q)) := by
    have h := congrArg (Polynomial.aeval (β : 𝓞 K)) hq
    simp only [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, minpoly.aeval,
      zero_sub] at h
    rw [mul_neg, ← h, neg_neg, eq_intCast]
  set m : ℤ := (minpoly ℤ (β : 𝓞 K)).coeff 0 with hm
  have hmS : ∀ x ∈ B, m • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro x hx
    rw [← Int.cast_smul_eq_zsmul (𝓞 K), hdiv, mul_smul]
    exact hβS _ (Submodule.smul_mem _ _ hx)
  have hfinB : Module.Finite ℤ B := by
    haveI : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr hB
    exact Module.Finite.trans (𝓞 K) B
  haveI hfg : AddGroup.FG B := Module.Finite.iff_addGroup_fg.mp hfinB
  let N : Submodule (𝓞 K) B := (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype
  haveI hfgQ : AddGroup.FG (B ⧸ N.toAddSubgroup) := by
    first
    | exact AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective N.toAddSubgroup)
    | exact QuotientAddGroup.fg N.toAddSubgroup
    | infer_instance
  have htors : IsAddTorsion (B ⧸ N.toAddSubgroup) := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H x =>
      refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨m.natAbs, Int.natAbs_pos.mpr hp0, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      show (m.natAbs • (x : Fin r → K)) ∈ Submodule.span (𝓞 K) (Set.range b)
      have e1 : (m.natAbs • (x : Fin r → K)) = ((m.natAbs : ℤ) • (x : Fin r → K)) := by simp
      rw [e1]
      rcases Int.natAbs_eq m with h | h
      · rw [← h]
        exact hmS _ x.2
      · rw [show ((m.natAbs : ℤ)) = -m by omega, neg_smul]
        exact Submodule.neg_mem _ (hmS _ x.2)
  have hfinQ : Finite (B ⧸ N.toAddSubgroup) := by
    first
    | exact AddCommGroup.finite_of_fg_torsion _ htors
    | exact AddCommGroup.finite_of_fg_torsion htors
  have : N.toAddSubgroup.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  exact this

theorem latDeg_le_of_le {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (C B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (hCB : C ≤ B) (hB : B.FG) (hbC : IsKBasisIn C b)
    (hbB : IsKBasisIn B b) : latDeg H C b ≤ latDeg H B b := by
  have hSC : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup ≤ C.toAddSubgroup := by
    intro x hx
    exact (Submodule.span_le.mpr (Set.range_subset_iff.mpr hbC.1)) hx
  have hCB' : C.toAddSubgroup ≤ B.toAddSubgroup := fun x hx => hCB hx
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hSC hCB'
  have hne : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup ≠ 0 :=
    spanIdx_ne_zero B b hB hbB
  have h1 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex C.toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hne) ⟨_, hmul.symm⟩
  have h2 : 0 < (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex C.toAddSubgroup := by
    refine Nat.pos_of_ne_zero fun h => hne ?_
    rw [← hmul, h, zero_mul]
  unfold latDeg
  have h3 : Real.log (((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex
      C.toAddSubgroup : ℕ) : ℝ) ≤ Real.log (((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex
      B.toAddSubgroup : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast h2) (by exact_mod_cast h1)
  linarith

theorem sum_log_norm_emb {K : Type} [Field K] [NumberField K] (a : K) :
    ∑ σ : K →+* ℂ, Real.log ‖σ a‖ = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  by_cases ha : a = 0
  · subst ha
    simp
  · have h1 : ((Algebra.norm ℚ a : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ a := by
      have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
      simp only [eq_ratCast] at h
      rw [h]
      exact Fintype.prod_bijective (fun σ : K →ₐ[ℚ] ℂ => (σ : K →+* ℂ))
        ⟨fun σ τ h => AlgHom.coe_ringHom_injective h,
          fun τ => ⟨τ.toRatAlgHom, RingHom.ext fun x => rfl⟩⟩ _ _ (fun σ => rfl)
    rw [← Real.log_prod (s := Finset.univ) (f := fun σ : K →+* ℂ => ‖σ a‖)
      (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ha)), ← norm_prod,
      ← h1]
    first
    | rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    | simp [Complex.norm_ratCast]
    | simp

def embMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun a i => σ (b i a)

theorem gramC_eq {K : Type} [Field K] [NumberField K] {r k : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    gramC H σ b = (embMat σ b)ᴴ * H * embMat σ b := by
  ext i j
  rw [Matrix.mul_assoc]
  simp [gramC, embMat, Matrix.mul_apply, Matrix.mulVec, dotProduct, embVec]

theorem embMat_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (hli : LinearIndependent K b) :
    Function.Injective (embMat σ b).mulVec := by
  classical
  let A : Matrix (Fin r) (Fin k) K := Matrix.of fun a i => b i a
  have hA : Function.Injective (Matrix.toLin' A) := by
    intro x y hxy
    have hinj : Function.Injective A.mulVec := by
      rw [Matrix.mulVec_injective_iff]
      exact hli
    exact hinj (by simpa [Matrix.toLin'_apply] using hxy)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A)
    (LinearMap.ker_eq_bot.mpr hA)
  have hBA : LinearMap.toMatrix' g * A = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h
  have hE : embMat σ b = A.map σ := by
    ext a i
    rfl
  have hBA' : (LinearMap.toMatrix' g).map σ * A.map σ = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one σ (map_zero σ) (map_one σ)]
  intro x y hxy
  rw [hE] at hxy
  have := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, hBA'] using this

theorem gramC_posDef {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : H.PosDef) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (hli : LinearIndependent K b) : (gramC H σ b).PosDef := by
  rw [gramC_eq]
  exact hH.conjTranspose_mul_mul_same (embMat_injective S σ b hli)

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def wPart (r m : ℕ) (i : Fin r) : Fin r :=
  if (i : ℕ) < m ∨ r ≤ (i : ℕ) + m then Fin.rev i else i

def wVal {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r) : K :=
  if (i : ℕ) < m ∨ r ≤ (i : ℕ) + m then 1 else g i

theorem wPart_wPart (r m : ℕ) (i : Fin r) : wPart r m (wPart r m i) = i := by
  have hi := i.isLt
  unfold wPart
  by_cases h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m
  · rw [if_pos h, if_pos (by simp only [Fin.val_rev]; omega), Fin.rev_rev]
  · rw [if_neg h, if_neg h]

theorem wPart_outer (r m : ℕ) (i : Fin r) (h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m) :
    wPart r m i = Fin.rev i := by
  unfold wPart
  rw [if_pos h]

theorem wPart_mid (r m : ℕ) (i : Fin r) (h : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m)) :
    wPart r m i = i := by
  unfold wPart
  rw [if_neg h]

theorem wVal_outer {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r)
    (h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m) : wVal r m g i = 1 := by
  unfold wVal
  rw [if_pos h]

theorem wVal_mid {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i : Fin r)
    (h : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m)) : wVal r m g i = g i := by
  unfold wVal
  rw [if_neg h]

theorem wittMat_eq {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) :
    wittMat r m g = Matrix.of fun i j => if j = wPart r m i then wVal r m g i else 0 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [wittMat, Matrix.of_apply]
  by_cases h : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m
  · rw [wPart_outer r m i h, wVal_outer r m g i h]
    by_cases hj' : j = Fin.rev i
    · subst hj'
      rw [if_pos rfl, if_pos (by simp only [Fin.val_rev]; omega)]
    · rw [if_neg hj']
      rw [if_neg (by rintro ⟨h1, -⟩; apply hj'; ext; simp only [Fin.val_rev]; omega),
        if_neg (by rintro ⟨rfl, h2, h3⟩; omega)]
  · rw [wPart_mid r m i h, wVal_mid r m g i h]
    by_cases hij : j = i
    · subst hij
      rw [if_pos rfl, if_neg (by rintro ⟨h1, h2⟩; omega), if_pos ⟨rfl, by omega, by omega⟩]
    · rw [if_neg hij, if_neg (by rintro ⟨h1, h2⟩; omega), if_neg (by rintro ⟨h1, -⟩; exact hij h1.symm)]

theorem wittMat_map_mul {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (σ : K →+* ℂ)
    (v : Fin r → ℂ) :
    (wittMat r m g).map σ * diagonal v * (wittMat r m g).map σ =
      diagonal fun i => σ (wVal r m g i) * v (wPart r m i) * σ (wVal r m g (wPart r m i)) := by
  rw [wittMat_eq]
  ext i k
  rw [Matrix.mul_apply, Finset.sum_eq_single (wPart r m i)]
  · simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.of_apply, if_pos rfl, wPart_wPart,
      Matrix.diagonal_apply]
    by_cases hik : i = k
    · subst hik
      simp
    · rw [if_neg (Ne.symm hik), if_neg hik, map_zero, mul_zero]
  · intro j _ hj
    simp only [Matrix.mul_diagonal, Matrix.map_apply, Matrix.of_apply, if_neg hj, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

def adMet {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K) (dd : Fin r → ℝ) :
    (K →+* ℂ) → Fin r → ℝ :=
  fun σ i => if (i : ℕ) < m then dd i else if r ≤ (i : ℕ) + m then (dd (Fin.rev i))⁻¹
    else ‖σ (g i)‖

theorem adMet_pos {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (hdd : ∀ i, 0 < dd i)
    (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) (σ : K →+* ℂ) (i : Fin r) :
    0 < adMet r m g dd σ i := by
  have hi := i.isLt
  unfold adMet
  split_ifs with h1 h2
  · exact hdd i
  · exact inv_pos.mpr (hdd _)
  · exact norm_pos_iff.mpr ((map_ne_zero σ).mpr (hg i (by omega) (by omega)))

theorem adMet_conj {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (σ : K →+* ℂ) :
    adMet r m g dd ((starRingEnd ℂ).comp σ) = adMet r m g dd σ := by
  funext i
  unfold adMet
  simp only [RingHom.comp_apply, Complex.norm_conj]

theorem wVal_adMet {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (h2m : 2 * m ≤ r)
    (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) (σ : K →+* ℂ)
    (hreal : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → conj (σ (g i)) = σ (g i))
    (i : Fin r) :
    σ (wVal r m g i) * (((adMet r m g dd σ (wPart r m i) : ℝ) : ℂ))⁻¹ *
      σ (wVal r m g (wPart r m i)) = ((adMet r m g dd σ i : ℝ) : ℂ) := by
  have hi := i.isLt
  by_cases h1 : (i : ℕ) < m
  · have ho : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m := Or.inl h1
    rw [wPart_outer r m i ho, wVal_outer r m g i ho,
      wVal_outer r m g (Fin.rev i) (by simp only [Fin.val_rev]; omega)]
    unfold adMet
    simp only [Fin.val_rev, Fin.rev_rev]
    rw [if_neg (show ¬ (r - ((i : ℕ) + 1) < m) by omega), if_pos (show r ≤ r - ((i : ℕ) + 1) + m by omega),
      if_pos h1]
    simp
  · by_cases h2 : r ≤ (i : ℕ) + m
    · have ho : (i : ℕ) < m ∨ r ≤ (i : ℕ) + m := Or.inr h2
      rw [wPart_outer r m i ho, wVal_outer r m g i ho,
        wVal_outer r m g (Fin.rev i) (by simp only [Fin.val_rev]; omega)]
      unfold adMet
      simp only [Fin.val_rev]
      rw [if_pos (show r - ((i : ℕ) + 1) < m by omega), if_neg h1, if_pos h2]
      simp
    · have hm : ¬ ((i : ℕ) < m ∨ r ≤ (i : ℕ) + m) := by omega
      rw [wPart_mid r m i hm, wVal_mid r m g i hm]
      unfold adMet
      rw [if_neg h1, if_neg h2]
      have hr := hreal i (by omega) (by omega)
      have hne : σ (g i) ≠ 0 := (map_ne_zero σ).mpr (hg i (by omega) (by omega))
      have hz : ((σ (g i)).re : ℂ) = σ (g i) := Complex.conj_eq_iff_re.mp hr
      rw [← hz, Complex.norm_real, Real.norm_eq_abs]
      have hx : (σ (g i)).re ≠ 0 := by
        intro h0
        apply hne
        rw [← hz, h0, Complex.ofReal_zero]
      have habs : ((|(σ (g i)).re| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hx
      have hsq : ((σ (g i)).re : ℂ) * (σ (g i)).re = ((|(σ (g i)).re| : ℝ) : ℂ) * |(σ (g i)).re| := by
        exact_mod_cast (abs_mul_abs_self (σ (g i)).re).symm
      calc ((σ (g i)).re : ℂ) * (↑|(σ (g i)).re|)⁻¹ * ((σ (g i)).re : ℂ)
          = (((σ (g i)).re : ℂ) * (σ (g i)).re) * (↑|(σ (g i)).re|)⁻¹ := by ring
        _ = (((|(σ (g i)).re| : ℝ) : ℂ) * |(σ (g i)).re|) * (↑|(σ (g i)).re|)⁻¹ := by rw [hsq]
        _ = ((|(σ (g i)).re| : ℝ) : ℂ) := by field_simp

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem herm_cGP {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (a b : Fin r) :
    S.c (((P.map S.c)ᵀ * S.G * P) a b) = ((P.map S.c)ᵀ * S.G * P) b a := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    S.c_invol, S.G_herm, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem g_fix {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K)
    (hJ : (P.map S.c)ᵀ * S.G * P = wittMat r m g) (i : Fin r) (h1 : m ≤ (i : ℕ))
    (h2 : (i : ℕ) + m < r) : S.c (g i) = g i := by
  have h := herm_cGP S P i i
  rw [hJ] at h
  simpa [wittMat, Matrix.of_apply, not_lt.2 h1, h1, h2] using h

theorem exists_adapted_majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K) (dd : Fin r → ℝ)
    (hP : P.det ≠ 0) (h2m : 2 * m ≤ r) (hJ : (P.map S.c)ᵀ * S.G * P = wittMat r m g)
    (hdd : ∀ i, 0 < dd i) (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) :
    ∃ M : Majorant S, ∀ σ,
      M.H σ = ((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ := by
  classical
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have hG : S.G = ((P⁻¹).map S.c)ᵀ * wittMat r m g * P⁻¹ := by
    rw [← hJ]
    have h1 : ((P⁻¹).map S.c)ᵀ * (P.map S.c)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hPP,
        Matrix.map_one _ (map_zero S.c) (map_one S.c), Matrix.transpose_one]
    calc S.G = ((P⁻¹).map S.c)ᵀ * (P.map S.c)ᵀ * S.G * (P * P⁻¹) := by
          rw [h1, hPP, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

  have key : ∀ σ : K →+* ℂ,
      let A := (P⁻¹).map σ
      let D := diagMet (adMet r m g dd) σ
      (Aᴴ * D * A).PosDef ∧ Aᴴ * D * A * (S.G.map σ)⁻¹ * (Aᴴ * D * A) = S.G.map σ := by
    intro σ A D
    set Ai := P.map σ with hAi
    have e1 : A * Ai = 1 := by
      simp only [A, Ai]
      rw [← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero σ) (map_one σ)]
    have e2 : Ai * A = 1 := by
      simp only [A, Ai]
      rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero σ) (map_one σ)]
    have e3 : Aiᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
    have e4 : Aᴴ * Aiᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]
    have hpos : ∀ i, 0 < adMet r m g dd σ i := adMet_pos r m g dd hdd hg σ
    let Dinv : Matrix (Fin r) (Fin r) ℂ :=
      diagonal fun i => (((adMet r m g dd σ i : ℝ) : ℂ))⁻¹
    have e5 : D * Dinv = 1 := by
      simp only [D, Dinv, diagMet, Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      have : ((adMet r m g dd σ i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos i).ne'
      exact mul_inv_cancel₀ this
    have hGσ : S.G.map σ = Aᴴ * (wittMat r m g).map σ * A := by
      rw [hG, Matrix.map_mul, Matrix.map_mul]
      congr 2
      ext a b
      simp [A, Matrix.conjTranspose_apply, S.c_emb]
    have hreal : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → conj (σ (g i)) = σ (g i) := by
      intro i h1 h2
      rw [← S.c_emb, g_fix S P m g hJ i h1 h2]
    have hKey : (wittMat r m g).map σ * Dinv * (wittMat r m g).map σ = D := by
      rw [wittMat_map_mul]
      simp only [D, diagMet]
      congr 1
      funext i
      exact wVal_adMet r m g dd h2m hg σ hreal i
    set Y := S.G.map σ with hY
    set Jσ := (wittMat r m g).map σ with hJσ
    set H := Aᴴ * D * A with hH
    set Hinv := Ai * Dinv * Aiᴴ with hHinv
    have hHH : H * Hinv = 1 := by
      calc H * Hinv = Aᴴ * D * (A * Ai) * Dinv * Aiᴴ := by simp only [H, Hinv, Matrix.mul_assoc]
        _ = Aᴴ * (D * Dinv) * Aiᴴ := by rw [e1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e5, Matrix.mul_one, e4]
    have hHH' : Hinv * H = 1 := mul_eq_one_comm.1 hHH
    have hYHY : Y * Hinv * Y = H := by
      rw [hGσ]
      calc Aᴴ * Jσ * A * Hinv * (Aᴴ * Jσ * A)
          = Aᴴ * Jσ * (A * Ai) * Dinv * (Aiᴴ * Aᴴ) * Jσ * A := by
            simp only [Hinv, Matrix.mul_assoc]
        _ = Aᴴ * (Jσ * Dinv * Jσ) * A := by
            rw [e1, e3, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = H := by rw [hKey]
    have hYinv : Y⁻¹ = Hinv * Y * Hinv := by
      apply Matrix.inv_eq_left_inv
      calc Hinv * Y * Hinv * Y = Hinv * (Y * Hinv * Y) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hYHY, hHH']
    refine ⟨?_, ?_⟩
    · have hD : D.PosDef := by
        simp only [D, diagMet]
        exact Matrix.posDef_diagonal_iff.2 fun i => by exact_mod_cast hpos i
      have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2
        (Matrix.isUnit_det_of_right_inverse e1)
      exact hD.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAu)
    · rw [hYinv]
      calc H * (Hinv * Y * Hinv) * H = (H * Hinv) * Y * (Hinv * H) := by
            simp only [Matrix.mul_assoc]
        _ = Y := by rw [hHH, hHH', Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨fun σ => ((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ,
    fun σ => (key σ).1, fun σ => (key σ).2, ?_⟩, fun σ => rfl⟩
  intro σ
  have hmap : (P⁻¹).map ((starRingEnd ℂ).comp σ) = ((P⁻¹).map σ).map (starRingEnd ℂ) := by
    rw [Matrix.map_map]
    rfl
  have hDc : diagMet (adMet r m g dd) ((starRingEnd ℂ).comp σ) =
      (diagMet (adMet r m g dd) σ).map (starRingEnd ℂ) := by
    simp only [diagMet, adMet_conj]
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    simp
  show ((P⁻¹).map ((starRingEnd ℂ).comp σ))ᴴ * diagMet (adMet r m g dd) ((starRingEnd ℂ).comp σ) *
      (P⁻¹).map ((starRingEnd ℂ).comp σ) =
    (((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ).map (starRingEnd ℂ)
  rw [hmap, hDc, Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map]
  intro x
  simp

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def matLin {K : Type} [Field K] [NumberField K] {r : ℕ} (Q : Matrix (Fin r) (Fin r) K) :
    (Fin r → K) →ₗ[𝓞 K] (Fin r → K) :=
  (Matrix.mulVecLin Q).restrictScalars (𝓞 K)

theorem matLin_apply {K : Type} [Field K] [NumberField K] {r : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (x : Fin r → K) : matLin Q x = Q *ᵥ x := rfl

theorem matLin_injective {K : Type} [Field K] [NumberField K] {r : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0) : Function.Injective (matLin Q) := by
  intro x y hxy
  rw [matLin_apply, matLin_apply] at hxy
  have hu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2 (isUnit_iff_ne_zero.2 hQ)
  exact (Matrix.mulVec_injective_iff_isUnit.2 hu) hxy

theorem span_mulVec {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (b : Fin k → Fin r → K) :
    Submodule.span (𝓞 K) (Set.range fun i => Q *ᵥ b i) =
      (Submodule.span (𝓞 K) (Set.range b)).map (matLin Q) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem latDeg_transport {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (D : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) :
    latDeg (fun σ => (Q.map σ)ᴴ * D σ * Q.map σ) B b =
      latDeg D (B.map (matLin Q)) (fun i => Q *ᵥ b i) := by
  unfold latDeg
  have hinj : Function.Injective (matLin Q) := matLin_injective Q hQ
  have h1 : (Submodule.span (𝓞 K) (Set.range fun i => Q *ᵥ b i)).toAddSubgroup.relIndex
      (B.map (matLin Q)).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup := by
    rw [span_mulVec, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hemb : ∀ (σ : K →+* ℂ) (x : Fin r → K), embVec σ (Q *ᵥ x) = Q.map σ *ᵥ embVec σ x := by
    intro σ x
    funext a
    exact RingHom.map_mulVec σ Q x a
  have h2 : ∀ σ : K →+* ℂ, gramC ((Q.map σ)ᴴ * D σ * Q.map σ) σ b = gramC (D σ) σ (fun i => Q *ᵥ b i) := by
    intro σ
    ext i j
    simp only [gramC, Matrix.of_apply, hemb]
    simp only [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  rw [h1]
  simp only [h2]

theorem kBasisIn_map {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (hb : IsKBasisIn B b) :
    IsKBasisIn (B.map (matLin Q)) (fun i => Q *ᵥ b i) := by
  obtain ⟨h1, h2, h3⟩ := hb
  have hinj : Function.Injective (Matrix.mulVecLin Q) := fun x y h => matLin_injective Q hQ h
  refine ⟨fun i => ⟨b i, h1 i, rfl⟩, ?_, ?_⟩
  · have e : (fun i => Q *ᵥ b i) = (Matrix.mulVecLin Q) ∘ b := rfl
    rw [e]
    exact h2.map' _ (LinearMap.ker_eq_bot.2 hinj)
  · rintro x ⟨y, hy, rfl⟩
    have h4 := Submodule.mem_map_of_mem (f := Matrix.mulVecLin Q) (h3 y hy)
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact h4

def formM {K : Type} [Field K] {r : ℕ} (c : K →+* K) (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) : K :=
  (fun a => c (x a)) ⬝ᵥ (M *ᵥ y)

theorem hermForm_h_eq {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h x y = formM S.c S.G x y := by
  unfold HermForm.h formM
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem formM_change {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (x y : Fin r → K) :
    formM S.c ((P.map S.c)ᵀ * S.G * P) x y = S.h (P *ᵥ x) (P *ᵥ y) := by
  rw [hermForm_h_eq]
  unfold formM
  have e1 : (fun a => S.c ((P *ᵥ x) a)) = (P.map S.c) *ᵥ (fun a => S.c (x a)) := by
    funext a
    exact RingHom.map_mulVec S.c P x a
  rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem formM_witt {K : Type} [Field K] {r : ℕ} (c : K →+* K) (m : ℕ) (g : Fin r → K)
    (x y : Fin r → K) :
    formM c (wittMat r m g) x y = ∑ a, c (x a) * (wVal r m g a * y (wPart r m a)) := by
  unfold formM
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  have ha := a.isLt
  by_cases h : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m
  · have hw : wVal r m g a = 1 := if_pos h
    have hp : wPart r m a = Fin.rev a := if_pos h
    rw [hw, hp, one_mul, Finset.sum_eq_single (Fin.rev a)]
    · rw [wittMat, Matrix.of_apply, if_pos, one_mul]
      rw [Fin.val_rev]
      omega
    · intro j _ hj
      rw [wittMat, Matrix.of_apply, if_neg, if_neg, zero_mul]
      · rintro ⟨rfl, h2, h3⟩
        omega
      · rintro ⟨h1, -⟩
        apply hj
        ext
        rw [Fin.val_rev]
        omega
    · simp
  · have hw : wVal r m g a = g a := if_neg h
    have hp : wPart r m a = a := if_neg h
    rw [hw, hp, Finset.sum_eq_single a]
    · rw [wittMat, Matrix.of_apply, if_neg, if_pos ⟨rfl, by omega, by omega⟩]
      omega
    · intro j _ hj
      rw [wittMat, Matrix.of_apply, if_neg, if_neg, zero_mul]
      · rintro ⟨rfl, -⟩
        exact hj rfl
      · have hj' := j.isLt
        omega
    · simp

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def IsAt {K : Type} [Field K] {r : ℕ} (i : Fin r) (x : Fin r → K) : Prop :=
  ∀ a, a ≠ i → x a = 0

theorem gramC_single {K : Type} [Field K] [NumberField K] {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ)
    (σ : K →+* ℂ) (i : Fin r) (x : Fin r → K) (hx : IsAt i x) :
    (gramC (diagMet δ σ) σ ![x]).det.re = ‖σ (x i)‖ ^ 2 * δ σ i := by
  rw [Matrix.det_unique]
  simp only [gramC, Matrix.of_apply, embVec, diagMet, Matrix.mulVec_diagonal, dotProduct,
    Pi.star_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Fin.default_eq_zero, Matrix.cons_val_zero]
    rw [show star (σ (x i)) * (((δ σ i : ℝ) : ℂ) * σ (x i)) =
        ((δ σ i : ℝ) : ℂ) * (starRingEnd ℂ (σ (x i)) * σ (x i)) by
      rw [Complex.star_def]; ring]
    rw [Complex.conj_mul']
    simp only [Complex.re_ofReal_mul]
    norm_cast
    ring
  · intro a _ ha
    simp [Fin.default_eq_zero, hx a ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem latDeg_single {K : Type} [Field K] [NumberField K] {r : ℕ}
    (δ : (K →+* ℂ) → Fin r → ℝ) (C : Submodule (𝓞 K) (Fin r → K)) (i : Fin r) (x : Fin r → K)
    (hx : IsAt i x) :
    latDeg (diagMet δ) C ![x] = Real.log (spanIdx C ![x] : ℝ) -
      (1 / 2) * ∑ σ : K →+* ℂ, Real.log (‖σ (x i)‖ ^ 2 * δ σ i) := by
  unfold latDeg spanIdx
  congr 2
  exact Finset.sum_congr rfl fun σ _ => by rw [gramC_single δ σ i x hx]

theorem sum_log_single {K : Type} [Field K] [NumberField K] (z : K) (hz : z ≠ 0) (d : ℝ)
    (hd : 0 < d) :
    ∑ σ : K →+* ℂ, Real.log (‖σ z‖ ^ 2 * d) =
      2 * Real.log |((Algebra.norm ℚ z : ℚ) : ℝ)| + (Fintype.card (K →+* ℂ) : ℝ) * Real.log d := by
  have h1 : ∀ σ : K →+* ℂ, Real.log (‖σ z‖ ^ 2 * d) = 2 * Real.log ‖σ z‖ + Real.log d := by
    intro σ
    have : ‖σ z‖ ≠ 0 := by simpa using hz
    rw [Real.log_mul (pow_ne_zero 2 this) hd.ne', Real.log_pow]
    push_cast
    ring
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum, sum_log_norm_emb, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

theorem kBasisIn_single {K : Type} [Field K] [NumberField K] {r : ℕ} (i : Fin r)
    (Gr : Submodule (𝓞 K) (Fin r → K)) (hat : ∀ x ∈ Gr, IsAt i x) (v : Fin r → K)
    (hv : v ∈ Gr) (hvi : v i ≠ 0) : IsKBasisIn Gr ![v] := by
  have hv0 : v ≠ 0 := fun h => hvi (by rw [h]; rfl)
  refine ⟨fun j => by fin_cases j; simpa using hv, ?_, ?_⟩
  · exact linearIndependent_unique_iff.2 (by simpa using hv0)
  · intro x hx
    rw [Set.range_unique, Submodule.mem_span_singleton]
    refine ⟨x i / v i, ?_⟩
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, Fin.default_eq_zero, Matrix.cons_val_zero]
    by_cases ha : a = i
    · subst ha
      field_simp
    · rw [hat x hx a ha, hat v hv a ha, mul_zero]

theorem rankOne_le_zero (hB : LatDegBasisStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ i, 0 < δ σ i) (i : Fin r)
    (Gr : Submodule (𝓞 K) (Fin r → K)) (hGr : Gr.FG) (hat : ∀ x ∈ Gr, IsAt i x)
    (x0 : Fin r → K) (hx0 : x0 ∈ Gr) (hx0i : x0 i ≠ 0)
    (hdeg : latDeg (diagMet δ) Gr ![x0] ≤ 0) (C : Submodule (𝓞 K) (Fin r → K)) (hC : C ≤ Gr)
    (k : ℕ) (c : Fin k → Fin r → K) (hc : IsKBasisIn C c) : latDeg (diagMet δ) C c ≤ 0 := by
  have hpd : ∀ σ, (diagMet δ σ).PosDef := fun σ =>
    Matrix.posDef_diagonal_iff.2 fun a => by exact_mod_cast hδ σ a
  have hci : ∀ j, c j i ≠ 0 := by
    intro j h0
    apply hc.2.1.ne_zero j
    funext a
    by_cases ha : a = i
    · subst ha; exact h0
    · exact hat _ (hC (hc.1 j)) a ha
  match k, c, hc, hci with
  | 0, c, hc, _ => exact (latDeg_zero_fam _ _ c hc).le
  | 1, c, hc, hci =>
    have hc1 : c = ![c 0] := by funext j; fin_cases j; rfl
    have hGc : IsKBasisIn Gr c := by
      rw [hc1]
      exact kBasisIn_single i Gr hat (c 0) (hC (hc.1 0)) (hci 0)
    calc latDeg (diagMet δ) C c ≤ latDeg (diagMet δ) Gr c :=
          latDeg_le_of_le _ C Gr c hC hGr hc hGc
      _ = latDeg (diagMet δ) Gr ![x0] :=
          hB K r 1 (diagMet δ) Gr c ![x0] hpd hGr hGc (kBasisIn_single i Gr hat x0 hx0 hx0i)
      _ ≤ 0 := hdeg
  | k + 2, c, hc, hci =>
    exfalso
    have hli := hc.2.1
    let t : Fin (k + 2) → K := fun j => if j = 0 then c 1 i else if j = 1 then -(c 0 i) else 0
    have ht : ∑ j, t j • c j = 0 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have h0 : ∀ j : Fin k, t j.succ.succ = 0 := fun j => by
        simp only [t]
        rw [if_neg (Fin.succ_ne_zero _), if_neg]
        intro h
        exact Fin.succ_ne_zero j (Fin.succ_injective _ h)
      simp only [h0, zero_smul, Finset.sum_const_zero, add_zero]
      have t0 : t 0 = c 1 i := by simp [t]
      have t1 : t (Fin.succ 0) = -(c 0 i) := by
        simp only [t]
        rw [if_neg (Fin.succ_ne_zero _)]
        rfl
      rw [t0, t1]
      funext a
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      by_cases ha : a = i
      · subst ha
        simp only [Fin.succ_zero_eq_one]
        ring
      · rw [hat _ (hC (hc.1 0)) a ha, hat _ (hC (hc.1 _)) a ha]
        ring
    have := Fintype.linearIndependent_iff.1 hli t ht 1
    simp [t] at this
    exact hci 0 this

theorem relIndex_sup_proj {G : Type} [AddCommGroup G] (π : G →+ G) (A X C : AddSubgroup G)
    (hXC : X ≤ C) (hA : ∀ a ∈ A, π a = 0) (hC : ∀ x ∈ C, π x = x) :
    (A ⊔ X).relIndex (A ⊔ C) = X.relIndex C := by
  have heq : A ⊔ X = X.comap π ⊓ (A ⊔ C) := by
    apply le_antisymm
    · refine le_inf (sup_le ?_ ?_) (sup_le_sup_left hXC A)
      · intro a ha
        show π a ∈ X
        rw [hA a ha]
        exact X.zero_mem
      · intro x hx
        show π x ∈ X
        rw [hC x (hXC hx)]
        exact hx
    · rintro z ⟨hzX, hz⟩
      obtain ⟨a, ha, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hz
      have hπ : π (a + w) = w := by rw [map_add, hA a ha, hC w hw, zero_add]
      have hwX : w ∈ X := by
        have : π (a + w) ∈ X := hzX
        rwa [hπ] at this
      exact AddSubgroup.add_mem_sup ha hwX
  have hmap : (A ⊔ C).map π = C := by
    rw [AddSubgroup.map_sup]
    have h1 : A.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨a, ha, rfl⟩
      rw [hA a ha]
      exact AddSubgroup.zero_mem _
    have h2 : C.map π = C := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        rw [hC x hx]
        exact hx
      · intro x hx
        exact ⟨x, hx, hC x hx⟩
    rw [h1, h2, bot_sup_eq]
  rw [heq, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, hmap]

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem isIntegralElt_add {K : Type} [Field K] [NumberField K] {x y : K} (hx : IsIntegralElt x)
    (hy : IsIntegralElt y) : IsIntegralElt (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

theorem isIntegralElt_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) {x : K}
    (hx : IsIntegralElt x) : IsIntegralElt (S.c x) := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨RingOfIntegers.mapRingHom S.c z, rfl⟩

theorem norm_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (z : K) :
    Algebra.norm ℚ (S.c z) = Algebra.norm ℚ z := by
  have hs : Function.Surjective S.c := fun x => ⟨S.c x, S.c_invol x⟩
  let e : K ≃+* K := RingEquiv.ofBijective S.c ⟨S.c.injective, hs⟩
  let e' : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := e) (fun q => by simp [e])
  exact Algebra.norm_eq_of_algEquiv e' z

def projLt (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if (i : ℕ) < e then x i else 0
  map_add' x y := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]

theorem spanIdx_pair {K : Type} [Field K] [NumberField K] {r : ℕ} (j p : Fin r)
    (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K)) (hj : ∀ x ∈ Gj, IsAt j x)
    (hp : ∀ x ∈ Gp, IsAt p x) (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hy : y ∈ Gp) :
    spanIdx (Gj ⊔ Gp) ![x0, y] = spanIdx Gj ![x0] * spanIdx Gp ![y] := by
  unfold spanIdx
  have hspan : Submodule.span (𝓞 K) (Set.range ![x0, y]) =
      Submodule.span (𝓞 K) {x0} ⊔ Submodule.span (𝓞 K) {y} := by
    rw [Matrix.range_cons_cons_empty, Submodule.span_insert]
  have h1 : Set.range ![x0] = {x0} := Matrix.range_cons_empty _ _
  have h2 : Set.range ![y] = {y} := Matrix.range_cons_empty _ _
  rw [hspan, h1, h2, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]
  set X0 := (Submodule.span (𝓞 K) {x0}).toAddSubgroup
  set Y := (Submodule.span (𝓞 K) {y}).toAddSubgroup
  have hX0 : X0 ≤ Gj.toAddSubgroup := by
    show Submodule.span (𝓞 K) {x0} ≤ Gj
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx0
  have hY : Y ≤ Gp.toAddSubgroup := by
    show Submodule.span (𝓞 K) {y} ≤ Gp
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hy
  have key := AddSubgroup.relIndex_mul_relIndex _ _ _ (sup_le_sup_left hY X0)
    (sup_le_sup_right hX0 Gp.toAddSubgroup)
  rw [← key, mul_comm (X0.relIndex _)]
  congr 1
  · refine relIndex_sup_proj (projGe K r p).toAddMonoidHom X0 Y Gp.toAddSubgroup hY ?_ ?_
    · intro a ha
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 ha
      show projGe K r p (t • x0) = 0
      rw [map_smul]
      have : projGe K r p x0 = 0 := by
        funext i
        show (if (p : ℕ) ≤ i then x0 i else 0) = 0
        split_ifs with h
        · exact hj x0 hx0 i (fun hi => by rw [hi] at h; omega)
        · rfl
      rw [this, smul_zero]
    · intro x hx
      show projGe K r p x = x
      funext i
      show (if (p : ℕ) ≤ i then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hp x hx i (fun hi => by rw [hi] at h; omega)).symm
  · rw [sup_comm X0, sup_comm Gj.toAddSubgroup]
    refine relIndex_sup_proj (projLt K r p).toAddMonoidHom Gp.toAddSubgroup X0 Gj.toAddSubgroup
      hX0 ?_ ?_
    · intro x hx
      show projLt K r p x = 0
      funext i
      show (if (i : ℕ) < p then x i else 0) = 0
      split_ifs with h
      · exact hp x hx i (fun hi => by rw [hi] at h; omega)
      · rfl
    · intro x hx
      show projLt K r p x = x
      funext i
      show (if (i : ℕ) < p then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hj x hx i (fun hi => by rw [hi] at h; omega)).symm

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def hypG {K : Type} [Field K] {r : ℕ} (j p : Fin r) : Matrix (Fin r) (Fin r) K :=
  Matrix.of fun a b => (if a = j ∧ b = p then 1 else 0) + (if a = p ∧ b = j then 1 else 0)

def hypForm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (j p : Fin r) :
    HermForm K r where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := hypG j p
  G_herm a b := by
    simp only [hypG, Matrix.of_apply, map_add, apply_ite S.c, map_one, map_zero]
    rw [add_comm]
    congr 1 <;> simp only [and_comm]

theorem hypForm_h {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (j p : Fin r)
    (x y : Fin r → K) : (hypForm S j p).h x y = S.c (x j) * y p + S.c (x p) * y j := by
  rw [HermForm.h]
  have e : ∀ a, ∑ b, (hypForm S j p).c (x a) * (hypForm S j p).G a b * y b =
      (if a = j then S.c (x a) * y p else 0) + (if a = p then S.c (x a) * y j else 0) := by
    intro a
    simp only [hypForm, hypG, Matrix.of_apply, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · by_cases ha : a = j <;> simp [ha]
    · by_cases ha : a = p <;> simp [ha]
  rw [Finset.sum_congr rfl fun a _ => e a]
  simp [Finset.sum_add_distrib]

theorem abs_norm_neg {K : Type} [Field K] [NumberField K] (z : K) :
    |((Algebra.norm ℚ (-z) : ℚ) : ℝ)| = |((Algebra.norm ℚ z : ℚ) : ℝ)| := by
  rw [neg_eq_neg_one_mul, map_mul, Rat.cast_mul, abs_mul]
  have h1 : (-1 : K) = algebraMap ℚ K (-1) := by simp
  rw [h1, Algebra.norm_algebraMap]
  simp

theorem top_le_zero (hN : IntegralIndexStatement) {K : Type} [Field K] [NumberField K] {r : ℕ}
    (S : HermForm K r) (j p : Fin r) (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K))
    (hGj : Gj.FG) (hGp : Gp.FG) (hj : ∀ x ∈ Gj, IsAt j x) (hp : ∀ x ∈ Gp, IsAt p x)
    (hpair : ∀ x ∈ Gj, ∀ y ∈ Gp, IsIntegralElt (S.c (x j) * y p))
    (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hx0j : x0 j ≠ 0) (hy : y ∈ Gp) (hyp : y p ≠ 0)
    (δ : (K →+* ℂ) → Fin r → ℝ) (d : ℝ) (hd : 0 < d) (hδj : ∀ σ, δ σ j = d)
    (hδp : ∀ σ, δ σ p = d⁻¹) (h0 : latDeg (diagMet δ) Gj ![x0] = 0) :
    latDeg (diagMet δ) Gp ![y] ≤ 0 := by
  have hjp' : j ≠ p := fun h => by rw [h] at hjp; omega
  have hx0p : x0 p = 0 := hj x0 hx0 p (Ne.symm hjp')
  have hyj : y j = 0 := hp y hy j hjp'

  set n : ℝ := (Fintype.card (K →+* ℂ) : ℝ)
  have e0 := h0
  rw [latDeg_single δ Gj j x0 (hj x0 hx0)] at e0
  simp only [hδj] at e0
  rw [sum_log_single (x0 j) hx0j d hd] at e0
  rw [latDeg_single δ Gp p y (hp y hy)]
  simp only [hδp]
  rw [sum_log_single (y p) hyp d⁻¹ (inv_pos.2 hd), Real.log_inv]

  set A : ℝ := (spanIdx Gj ![x0] : ℝ)
  set B : ℝ := (spanIdx Gp ![y] : ℝ)
  set X : ℝ := |((Algebra.norm ℚ (x0 j) : ℚ) : ℝ)|
  set Y : ℝ := |((Algebra.norm ℚ (y p) : ℚ) : ℝ)|
  have hA : 1 ≤ A := by
    have := spanIdx_ne_zero Gj ![x0] hGj (kBasisIn_single j Gj hj x0 hx0 hx0j)
    exact Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)
  have hB : 1 ≤ B := by
    have := spanIdx_ne_zero Gp ![y] hGp (kBasisIn_single p Gp hp y hy hyp)
    exact Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 this)
  have hX : 0 < X := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hx0j
  have hY : 0 < Y := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hyp
  have key : A * B ≤ X * Y := by
    set T := Gj ⊔ Gp
    have hT : T.FG := hGj.sup hGp
    have hbT : IsKBasisIn T ![x0, y] := by
      refine ⟨fun i => ?_, ?_, ?_⟩
      · fin_cases i
        · exact Submodule.mem_sup_left hx0
        · exact Submodule.mem_sup_right hy
      · rw [LinearIndependent.pair_iff]
        intro s t hst
        have h1 := congr_fun hst j
        have h2 := congr_fun hst p
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hx0p, hyj,
          mul_zero, add_zero, zero_add] at h1 h2
        exact ⟨(mul_eq_zero.1 h1).resolve_right hx0j, (mul_eq_zero.1 h2).resolve_right hyp⟩
      · intro z hz
        obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
        rw [Matrix.range_cons_cons_empty]
        have e1 : z1 = (z1 j / x0 j) • x0 := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases ha : a = j
          · subst ha; field_simp
          · rw [hj z1 hz1 a ha, hj x0 hx0 a ha, mul_zero]
        have e2 : z2 = (z2 p / y p) • y := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          by_cases ha : a = p
          · subst ha; field_simp
          · rw [hp z2 hz2 a ha, hp y hy a ha, mul_zero]
        rw [e1, e2]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hint : IsIntegralOn (hypForm S j p) T := by
      intro z hz w hw
      obtain ⟨z1, hz1, z2, hz2, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨w1, hw1, w2, hw2, rfl⟩ := Submodule.mem_sup.1 hw
      rw [hypForm_h]
      simp only [Pi.add_apply, hj z1 hz1 p (Ne.symm hjp'), hj w1 hw1 p (Ne.symm hjp'),
        hp z2 hz2 j hjp', hp w2 hw2 j hjp', add_zero, zero_add]
      refine isIntegralElt_add (hpair z1 hz1 w2 hw2) ?_
      have := isIntegralElt_c S (hpair w1 hw1 z2 hz2)
      rwa [map_mul, S.c_invol, mul_comm] at this
    have hgram : hGram (hypForm S j p) ![x0, y] =
        !![0, S.c (x0 j) * y p; S.c (y p) * x0 j, 0] := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [hGram, hypForm_h, hx0p, hyj]
    have hdet : (hGram (hypForm S j p) ![x0, y]).det = -((S.c (x0 j) * y p) * (S.c (y p) * x0 j)) := by
      rw [hgram, Matrix.det_fin_two_of]
      ring
    have hcx : S.c (x0 j) ≠ 0 := fun h => hx0j (S.c.injective (by rw [h, map_zero]))
    have hcy : S.c (y p) ≠ 0 := fun h => hyp (S.c.injective (by rw [h, map_zero]))
    have hdet0 : (hGram (hypForm S j p) ![x0, y]).det ≠ 0 := by
      rw [hdet, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero hcx hyp) (mul_ne_zero hcy hx0j)
    have hb := hN K r 2 (hypForm S j p) T ![x0, y] hT hbT hint hdet0
    rw [hdet, abs_norm_neg, map_mul, map_mul, map_mul, norm_c, norm_c] at hb
    push_cast at hb
    rw [spanIdx_pair j p hjp Gj Gp hj hp x0 y hx0 hy] at hb
    push_cast at hb
    have hb' : (A * B) ^ 2 ≤ (X * Y) ^ 2 :=
      le_of_le_of_eq hb (by simp only [X, Y]; rw [abs_mul, abs_mul, abs_mul]; ring)
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hb'
  have hlog : Real.log A + Real.log B ≤ Real.log X + Real.log Y := by
    rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_mul hX.ne' hY.ne']
    exact Real.log_le_log (by positivity) key
  linarith

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def colMat {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) K :=
  Matrix.of fun a i => b i a

theorem hGram_eq {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : hGram S b = ((colMat b).map S.c)ᵀ * S.G * colMat b := by
  ext i j
  simp only [hGram, HermForm.h, colMat, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem colMat_mulVec {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) (t : Fin k → K) :
    colMat b *ᵥ t = ∑ j, t j • b j := by
  funext a
  simp [colMat, mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem form_colMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) (t : Fin k → K) :
    (fun i => S.c (t i)) ⬝ᵥ (hGram S b *ᵥ t) = S.h (colMat b *ᵥ t) (colMat b *ᵥ t) := by
  rw [hGram_eq, hermForm_h_eq]
  simp only [formM]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]
  congr 1
  funext a
  rw [RingHom.map_mulVec]
  rfl

theorem hermForm_swap {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.c (S.h x y) = S.h y x := by
  simp only [HermForm.h, map_sum, map_mul, S.c_invol]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [S.G_herm]
  ring

theorem quad_eq {r k : ℕ} (E : Matrix (Fin r) (Fin k) ℂ) (X : Matrix (Fin r) (Fin r) ℂ)
    (v : Fin k → ℂ) : star v ⬝ᵥ ((Eᴴ * X * E) *ᵥ v) = star (E *ᵥ v) ⬝ᵥ (X *ᵥ (E *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

theorem quad_diag {r : ℕ} (d w : Fin r → ℂ) :
    star w ⬝ᵥ (diagonal d *ᵥ w) = ∑ a, d a * ((‖w a‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul', Complex.star_def]
  ring

def midG {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  Matrix.diagonal fun a => if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0

def midForm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a) :
    HermForm K r where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := midG r m g
  G_herm a b := by
    by_cases hab : a = b
    · subst hab
      simp only [midG, Matrix.diagonal_apply_eq]
      split_ifs with h
      · exact hfix a h.1 h.2
      · exact map_zero _
    · simp [midG, Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem mid_le_zero (hN : IntegralIndexStatement) (hA : AbsDetStatement) {K : Type} [Field K]
    [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ) (g : Fin r → K)
    (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (Gm : Submodule (𝓞 K) (Fin r → K)) (hGm : Gm.FG)
    (hsupp : ∀ x ∈ Gm, ∀ a : Fin r, ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → x a = 0)
    (hint : IsIntegralOn (midForm S m g hfix) Gm)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0)
    (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ a, 0 < δ σ a)
    (hδmid : ∀ σ (a : Fin r), m ≤ (a : ℕ) → (a : ℕ) + m < r → δ σ a = ‖σ (g a)‖)
    (C : Submodule (𝓞 K) (Fin r → K)) (hC : C ≤ Gm) (k : ℕ) (c : Fin k → Fin r → K)
    (hc : IsKBasisIn C c) : latDeg (diagMet δ) C c ≤ 0 := by
  set Sm := midForm S m g hfix with hSm
  have hCfg : C.FG := Submodule.FG.of_le hGm hC
  have hCint : IsIntegralOn Sm C := fun x hx y hy => hint x (hC hx) y (hC hy)

  have hSmh : ∀ z : Fin r → K, (∀ a : Fin r, ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → z a = 0) →
      Sm.h z z = ∑ a, S.c (z a) * g a * z a := by
    intro z hz
    simp only [HermForm.h, hSm, midForm, midG, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · rfl
    · rw [hz a (by omega)]
      simp
  have hdet : (hGram Sm c).det ≠ 0 := by
    intro h0
    obtain ⟨t, ht0, ht⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    set z := colMat c *ᵥ t with hz
    have hzsupp : ∀ a : Fin r, ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → z a = 0 := by
      intro a ha
      rw [hz, colMat_mulVec, Finset.sum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Pi.smul_apply, hsupp _ (hC (hc.1 j)) a ha, smul_zero]
    have h1 : Sm.h z z = 0 := by
      rw [hz, ← form_colMat, ht]
      simp
    rw [hSmh z hzsupp] at h1
    have h2 := haniso z hzsupp h1
    rw [hz, colMat_mulVec] at h2
    exact ht0 (funext (Fintype.linearIndependent_iff.1 hc.2.1 t h2))
  have hidx := hN K r k Sm C c hCfg hc hCint hdet
  have hDpd : ∀ σ, (diagMet δ σ).PosDef := fun σ =>
    Matrix.posDef_diagonal_iff.2 fun a => by exact_mod_cast hδ σ a

  have hσ : ∀ σ : K →+* ℂ, ‖σ (hGram Sm c).det‖ ≤ (gramC (diagMet δ σ) σ c).det.re := by
    intro σ
    set E := embMat σ c with hE
    have hEc : ((colMat c).map S.c)ᵀ.map σ = Eᴴ := by
      ext a b
      simp [hE, embMat, colMat, Matrix.conjTranspose_apply, S.c_emb]
    have hC' : (hGram Sm c).map σ = Eᴴ * (midG r m g).map σ * E := by
      rw [hGram_eq, Matrix.map_mul, Matrix.map_mul]
      simp only [hSm, midForm]
      rw [hEc]
      rfl
    have hGσ : (midG r m g).map σ =
        diagonal fun a : Fin r => σ (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0) := by
      simp only [midG]
      rw [Matrix.diagonal_map (map_zero σ)]
    have hherm : ((hGram Sm c).map σ).IsHermitian := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply, hGram, Matrix.of_apply]
      rw [← hermForm_swap Sm (c j) (c i), Sm.c_emb]
      rfl
    have hineq : ∀ v : Fin k → ℂ, ‖star v ⬝ᵥ (((hGram Sm c).map σ) *ᵥ v)‖ ≤
        (star v ⬝ᵥ ((gramC (diagMet δ σ) σ c) *ᵥ v)).re := by
      intro v
      rw [hC', gramC_eq, quad_eq, quad_eq, hGσ]
      simp only [diagMet]
      rw [quad_diag, quad_diag]
      calc ‖∑ a : Fin r, σ (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0) *
              ((‖(E *ᵥ v) a‖ ^ 2 : ℝ) : ℂ)‖
          ≤ ∑ a : Fin r, ‖σ (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then g a else 0) *
              ((‖(E *ᵥ v) a‖ ^ 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ a : Fin r, δ σ a * ‖(E *ᵥ v) a‖ ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            gcongr
            split_ifs with h
            · rw [hδmid σ a h.1 h.2]
            · simp only [map_zero, norm_zero]
              exact (hδ σ a).le
        _ = (∑ a : Fin r, ((δ σ a : ℝ) : ℂ) * ((‖(E *ᵥ v) a‖ ^ 2 : ℝ) : ℂ)).re := by
            rw [Complex.re_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Complex.ofReal_mul, Complex.ofReal_re]
    have h5 := hA k (gramC (diagMet δ σ) σ c) ((hGram Sm c).map σ)
      (gramC_posDef S _ (hDpd σ) σ c hc.2.1) hherm hineq
    rwa [show ((hGram Sm c).map σ).det = σ (hGram Sm c).det from (RingHom.map_det σ _).symm] at h5
  have hN0 : 0 < |((Algebra.norm ℚ (hGram Sm c).det : ℚ) : ℝ)| := by
    apply abs_pos.2
    exact_mod_cast (Algebra.norm_ne_zero_iff).2 hdet
  have hsum : Real.log |((Algebra.norm ℚ (hGram Sm c).det : ℚ) : ℝ)| ≤
      ∑ σ : K →+* ℂ, Real.log (gramC (diagMet δ σ) σ c).det.re := by
    rw [← sum_log_norm_emb]
    refine Finset.sum_le_sum fun σ _ => Real.log_le_log ?_ (hσ σ)
    apply norm_pos_iff.2
    intro h0
    exact hdet (σ.injective (by rw [h0, map_zero]))
  have hone : 1 ≤ (spanIdx C c : ℝ) :=
    Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (spanIdx_ne_zero C c hCfg hc))
  have hidx' : 2 * Real.log (spanIdx C c : ℝ) ≤ Real.log |((Algebra.norm ℚ (hGram Sm c).det : ℚ) : ℝ)| := by
    have := Real.log_le_log (by positivity) hidx
    rwa [Real.log_pow] at this
  unfold latDeg
  unfold spanIdx at hidx'
  linarith

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem gr_at {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (j : Fin r) : ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), IsAt j x := by
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩ a ha
  show (if (j : ℕ) ≤ a then y a else 0) = 0
  split_ifs with h
  · exact hy a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)
  · rfl

theorem exists_at {K : Type} [Field K] [NumberField K] {r : ℕ} (Lp : Submodule (𝓞 K) (Fin r → K))
    (hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp) (j : Fin r) :
    ∃ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j), x j ≠ 0 := by
  obtain ⟨a, ha, hav⟩ := hsp (Pi.single j 1)
  have hcut : a • (Pi.single j 1 : Fin r → K) ∈ cutSub K r (j + 1) := by
    intro i hi
    have : i ≠ j := fun e => by rw [e] at hi; omega
    simp [this]
  refine ⟨projGe K r j (a • Pi.single j 1), ⟨_, ⟨hav, hcut⟩, rfl⟩, ?_⟩
  show (if (j : ℕ) ≤ j then (a • (Pi.single j 1 : Fin r → K)) j else 0) ≠ 0
  rw [if_pos le_rfl]
  simpa using ha

theorem pair_int {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (h2m : 2 * m ≤ r) (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y))
    (j : Fin r) (hj : (j : ℕ) < m) :
    ∀ x ∈ (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j),
      ∀ y ∈ (Lp ⊓ cutSub K r (Fin.rev j + 1)).map (projGe K r (Fin.rev j)),
        IsIntegralElt (S.c (x j) * y (Fin.rev j)) := by
  rintro _ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩
  have hrev := Fin.val_rev j
  have hj' := j.isLt
  have e1 : projGe K r j x j = x j := by
    show (if (j : ℕ) ≤ j then x j else 0) = x j
    rw [if_pos le_rfl]
  have e2 : projGe K r (Fin.rev j) y (Fin.rev j) = y (Fin.rev j) := by
    show (if ((Fin.rev j : Fin r) : ℕ) ≤ (Fin.rev j : Fin r) then y (Fin.rev j) else 0) = _
    rw [if_pos le_rfl]
  rw [e1, e2]
  have h := hint x hxL y hyL
  rw [formM_witt, Finset.sum_eq_single j] at h
  · rwa [wVal_outer r m g j (Or.inl hj), wPart_outer r m j (Or.inl hj), one_mul] at h
  · intro a _ ha
    by_cases hlt : (a : ℕ) < j
    · have hao : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m := Or.inl (by omega)
      rw [wPart_outer r m a hao]
      have : y (Fin.rev a) = 0 := hyc _ (by rw [Fin.val_rev, Fin.val_rev]; omega)
      rw [this, mul_zero, mul_zero]
    · have : x a = 0 := hxc a (by have : (a : ℕ) ≠ j := fun e => ha (Fin.ext e); omega)
      rw [this, map_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mid_supp {K : Type} [Field K] [NumberField K] {r : ℕ} (m : ℕ)
    (Lp : Submodule (𝓞 K) (Fin r → K)) :
    ∀ x ∈ (Lp ⊓ cutSub K r (r - m)).map (projGe K r m), ∀ a : Fin r,
      ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) → x a = 0 := by
  rintro _ ⟨y, ⟨_, hy⟩, rfl⟩ a ha
  show (if m ≤ (a : ℕ) then y a else 0) = 0
  split_ifs with h
  · exact hy a (by omega)
  · rfl

theorem mid_int {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (m : ℕ)
    (g : Fin r → K) (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (Lp : Submodule (𝓞 K) (Fin r → K))
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y)) :
    IsIntegralOn (midForm S m g hfix) ((Lp ⊓ cutSub K r (r - m)).map (projGe K r m)) := by
  rintro _ ⟨x, ⟨hxL, hxc⟩, rfl⟩ _ ⟨y, ⟨hyL, hyc⟩, rfl⟩
  have h := hint x hxL y hyL
  convert h using 1
  rw [formM_witt]
  simp only [HermForm.h, midForm, midG, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha := a.isLt
  show (if m ≤ (a : ℕ) ∧ (a : ℕ) + m < r then
      S.c (if m ≤ (a : ℕ) then x a else 0) * g a * (if m ≤ (a : ℕ) then y a else 0)
      else 0) = _
  by_cases hmid : m ≤ (a : ℕ) ∧ (a : ℕ) + m < r
  · have ho : ¬ ((a : ℕ) < m ∨ r ≤ (a : ℕ) + m) := by omega
    simp only [if_pos hmid, if_pos hmid.1]
    rw [wVal_mid r m g a ho, wPart_mid r m a ho]
    ring
  · rw [if_neg hmid]
    by_cases hlt : (a : ℕ) < m
    · have ho : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m := Or.inl hlt
      rw [wPart_outer r m a ho]
      have : y (Fin.rev a) = 0 := hyc _ (by rw [Fin.val_rev]; omega)
      rw [this, mul_zero, mul_zero]
    · have : x a = 0 := hxc a (by omega)
      rw [this, map_zero, zero_mul]

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem cutSub_zero (K : Type) [Field K] [NumberField K] (r : ℕ) : cutSub K r 0 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  funext i
  exact hx i (Nat.zero_le _)

theorem cutSub_self (K : Type) [Field K] [NumberField K] (r : ℕ) : cutSub K r r = ⊤ := by
  rw [eq_top_iff]
  intro x _ i hi
  exact absurd i.isLt (by omega)

theorem flag_base {K : Type} [Field K] [NumberField K] {r : ℕ}
    (D : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (Lp : Submodule (𝓞 K) (Fin r → K)) :
    ∀ B ≤ Lp ⊓ cutSub K r 0, ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b →
      latDeg D B b ≤ 0 := by
  intro B hB k b hb
  have hB0 : B = ⊥ := eq_bot_iff.2 (hB.trans (inf_le_right.trans (by rw [cutSub_zero])))
  subst hB0
  have hk := kBasisIn_bot_eq b hb
  subst hk
  exact (latDeg_zero_fam D ⊥ b hb).le

theorem flag_step (hE : GradedExtStatement) {K : Type} [Field K] [NumberField K] {r : ℕ}
    (δ : (K →+* ℂ) → Fin r → ℝ) (hδ : ∀ σ i, 0 < δ σ i) (Lp : Submodule (𝓞 K) (Fin r → K))
    (hLp : Lp.FG) (e' e : ℕ)
    (hP : ∀ B ≤ Lp ⊓ cutSub K r e', ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b →
      latDeg (diagMet δ) B b ≤ 0)
    (hG : ∀ C ≤ (Lp ⊓ cutSub K r e).map (projGe K r e'), ∀ (k : ℕ) (c : Fin k → Fin r → K),
      IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0) :
    ∀ B ≤ Lp ⊓ cutSub K r e, ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b →
      latDeg (diagMet δ) B b ≤ 0 := by
  intro B hB k b hb
  have hBfg : B.FG := Submodule.FG.of_le hLp (hB.trans inf_le_left)
  obtain ⟨k0, b0, hb0⟩ := exists_kBasisIn (B ⊓ cutSub K r e')
  obtain ⟨k1, b1, hb1⟩ := exists_kBasisIn (B.map (projGe K r e'))
  have h := hE K r e' k k0 k1 δ B b b0 b1 hδ hBfg hb hb0 hb1
  have h0 := hP (B ⊓ cutSub K r e') (inf_le_inf_right _ (hB.trans inf_le_left)) k0 b0 hb0
  have h1 := hG (B.map (projGe K r e')) (Submodule.map_mono hB) k1 b1 hb1
  linarith

theorem adapted_semistable (hB : LatDegBasisStatement) (hN : IntegralIndexStatement)
    (hA : AbsDetStatement) (hE : GradedExtStatement) {K : Type} [Field K] [NumberField K]
    {r : ℕ} (S : HermForm K r) (m : ℕ) (g : Fin r → K) (h2m : 2 * m ≤ r)
    (hfix : ∀ a : Fin r, m ≤ (a : ℕ) → (a : ℕ) + m < r → S.c (g a) = g a)
    (hg0 : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0)
    (haniso : ∀ t : Fin r → K, (∀ i : Fin r, (i : ℕ) < m ∨ r ≤ (i : ℕ) + m → t i = 0) →
      ∑ i, S.c (t i) * g i * t i = 0 → t = 0)
    (Lp : Submodule (𝓞 K) (Fin r → K)) (hLp : Lp.FG)
    (hsp : ∀ v : Fin r → K, ∃ a : 𝓞 K, a ≠ 0 ∧ a • v ∈ Lp)
    (hint : ∀ x ∈ Lp, ∀ y ∈ Lp, IsIntegralElt (formM S.c (wittMat r m g) x y)) :
    ∃ dd : Fin r → ℝ, (∀ i, 0 < dd i) ∧ ∀ B ≤ Lp, ∀ (k : ℕ) (b : Fin k → Fin r → K),
      IsKBasisIn B b → latDeg (diagMet (adMet r m g dd)) B b ≤ 0 := by
  classical
  choose x0 hx0 hx0j using exists_at Lp hsp
  have hn : (0 : ℝ) < (Fintype.card (K →+* ℂ) : ℝ) := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card (K →+* ℂ) : ℝ) with hn_def
  let Gr : Fin r → Submodule (𝓞 K) (Fin r → K) := fun j =>
    (Lp ⊓ cutSub K r (j + 1)).map (projGe K r j)
  have hGrfg : ∀ j, (Gr j).FG := fun j => (Submodule.FG.of_le hLp inf_le_left).map _
  let dd : Fin r → ℝ := fun j => Real.exp ((2 / n) * (Real.log (spanIdx (Gr j) ![x0 j] : ℝ) -
    Real.log |((Algebra.norm ℚ (x0 j j) : ℚ) : ℝ)|))
  have hdd : ∀ j, 0 < dd j := fun j => Real.exp_pos _
  refine ⟨dd, hdd, ?_⟩
  set δ := adMet r m g dd with hδdef
  have hδ : ∀ σ a, 0 < δ σ a := adMet_pos r m g dd hdd hg0
  have hbot0 : ∀ j : Fin r, (j : ℕ) < m → latDeg (diagMet δ) (Gr j) ![x0 j] = 0 := by
    intro j hj
    rw [latDeg_single δ _ j (x0 j) (gr_at Lp j _ (hx0 j))]
    have hδj : ∀ σ, δ σ j = dd j := fun σ => by simp [hδdef, adMet, hj]
    simp only [hδj]
    rw [sum_log_single (x0 j j) (hx0j j) (dd j) (hdd j), Real.log_exp]
    field_simp
    ring

  have hGb : ∀ j : Fin r, (j : ℕ) < m → ∀ C ≤ Gr j, ∀ (k : ℕ) (c : Fin k → Fin r → K),
      IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0 := fun j hj C hC k c hc =>
    rankOne_le_zero hB δ hδ j (Gr j) (hGrfg j) (gr_at Lp j) (x0 j) (hx0 j) (hx0j j)
      (hbot0 j hj).le C hC k c hc
  have hGt : ∀ p : Fin r, r ≤ (p : ℕ) + m → ∀ C ≤ Gr p, ∀ (k : ℕ) (c : Fin k → Fin r → K),
      IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0 := by
    intro p hp C hC k c hc
    have hpr := p.isLt
    have hjv : ((Fin.rev p : Fin r) : ℕ) = r - (p + 1) := Fin.val_rev p
    have hj : ((Fin.rev p : Fin r) : ℕ) < m := by omega
    have hpj : Fin.rev (Fin.rev p) = p := Fin.rev_rev p
    have hjp : ((Fin.rev p : Fin r) : ℕ) < p := by omega
    have hpair := pair_int S m g h2m Lp hint (Fin.rev p) hj
    rw [hpj] at hpair
    have hδj : ∀ σ, δ σ (Fin.rev p) = dd (Fin.rev p) := fun σ => by
      show adMet r m g dd σ (Fin.rev p) = _
      unfold adMet
      rw [if_pos hj]
    have hδp : ∀ σ, δ σ p = (dd (Fin.rev p))⁻¹ := fun σ => by
      have h1 : ¬ (p : ℕ) < m := by omega
      simp [hδdef, adMet, h1, hp]
    have htop := top_le_zero hN S (Fin.rev p) p hjp (Gr (Fin.rev p)) (Gr p) (hGrfg _) (hGrfg p)
      (gr_at Lp _) (gr_at Lp p) hpair (x0 (Fin.rev p)) (x0 p) (hx0 _) (hx0j _) (hx0 p) (hx0j p)
      δ (dd (Fin.rev p)) (hdd _) hδj hδp (hbot0 _ hj)
    exact rankOne_le_zero hB δ hδ p (Gr p) (hGrfg p) (gr_at Lp p) (x0 p) (hx0 p) (hx0j p) htop
      C hC k c hc
  have hGm : ∀ C ≤ (Lp ⊓ cutSub K r (r - m)).map (projGe K r m), ∀ (k : ℕ)
      (c : Fin k → Fin r → K), IsKBasisIn C c → latDeg (diagMet δ) C c ≤ 0 := by
    intro C hC k c hc
    have hδmid : ∀ σ (a : Fin r), m ≤ (a : ℕ) → (a : ℕ) + m < r → δ σ a = ‖σ (g a)‖ := by
      intro σ a h1 h2
      have h1' : ¬ (a : ℕ) < m := by omega
      have h2' : ¬ r ≤ (a : ℕ) + m := by omega
      simp [hδdef, adMet, h1', h2']
    exact mid_le_zero hN hA S m g hfix _ ((Submodule.FG.of_le hLp inf_le_left).map _)
      (mid_supp m Lp) (mid_int S m g hfix Lp hint) haniso δ hδ hδmid C hC k c hc

  have P1 : ∀ e, e ≤ m → ∀ B ≤ Lp ⊓ cutSub K r e, ∀ (k : ℕ) (b : Fin k → Fin r → K),
      IsKBasisIn B b → latDeg (diagMet δ) B b ≤ 0 := by
    intro e
    induction e with
    | zero => intro _; exact flag_base _ Lp
    | succ e ih =>
      intro he
      exact flag_step hE δ hδ Lp hLp e (e + 1) (ih (by omega))
        (hGb ⟨e, by omega⟩ (by show e < m; omega))
  have P2 := flag_step hE δ hδ Lp hLp m (r - m) (P1 m le_rfl) hGm
  have P3 : ∀ t, t ≤ m → ∀ B ≤ Lp ⊓ cutSub K r (r - m + t), ∀ (k : ℕ)
      (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg (diagMet δ) B b ≤ 0 := by
    intro t
    induction t with
    | zero => intro _; simpa using P2
    | succ t ih =>
      intro ht
      exact flag_step hE δ hδ Lp hLp (r - m + t) (r - m + t + 1) (ih (by omega))
        (hGt ⟨r - m + t, by omega⟩ (by show r ≤ r - m + t + m; omega))
  intro B hB k b hb
  have hrm : r - m + m = r := by omega
  have := P3 m le_rfl
  rw [hrm, cutSub_self, inf_top_eq] at this
  exact this B hB k b hb

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end
