import Mathlib
import Formalism.PeriodIntegrals.IdxCalc
import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic

section
noncomputable section

namespace PI.Dv.ProjGramW

open NumberField IsDedekindDomain Formalism.BasicNotions

def IdxDet : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (d : ℕ) (b : Fin d → V),
    LinearIndependent K b → ∀ C : Matrix (Fin d) (Fin d) K, C.det ≠ 0 →
    idxAt w (Submodule.span (𝓞 K) (Set.range b))
      (Submodule.span (𝓞 K) (Set.range fun j => ∑ i, C i j • b i)) = vAdd w C.det

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

lemma idxAt_antisymm (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) :
    idxAt w M N = - idxAt w N M := by
  unfold PI.Dv.idxAt
  ring

lemma locLe_zero_iff (w : HeightOneSpectrum (𝓞 K)) (X Y : Submodule (𝓞 K) V) :
    LocLe w 0 X Y ↔ ∀ x ∈ X, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ Y := by
  unfold PI.Dv.LocLe
  simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

lemma algebraMap_ne_zero_of_not_mem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  intro h0
  apply hs
  have : s = 0 := (IsFractionRing.injective (𝓞 K) K) (h0.trans (map_zero _).symm)
  rw [this]
  exact w.asIdeal.zero_mem

lemma span_le_of_locLe (w : HeightOneSpectrum (𝓞 K)) {X Y : Submodule (𝓞 K) V} (h : LocLe w 0 X Y) :
    Submodule.span K (X : Set V) ≤ Submodule.span K (Y : Set V) := by
  rw [Submodule.span_le]
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (locLe_zero_iff w X Y).mp h x hx
  have hs0 := algebraMap_ne_zero_of_not_mem w hs
  have h1 : (algebraMap (𝓞 K) K s) • x ∈ Submodule.span K (Y : Set V) := by
    rw [algebraMap_smul]
    exact Submodule.subset_span hsx
  have h2 := Submodule.smul_mem (Submodule.span K (Y : Set V)) (algebraMap (𝓞 K) K s)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at h2

lemma idx_eq_zero_of_loc (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {X Y : Submodule (𝓞 K) V}
    (hX : X.FG) (hY : Y.FG) (hXY : LocLe w 0 X Y) (hYX : LocLe w 0 Y X) : idxAt w X Y = 0 := by
  have hs : Submodule.span K (X : Set V) = Submodule.span K (Y : Set V) :=
    le_antisymm (span_le_of_locLe w hXY) (span_le_of_locLe w hYX)
  have h1 := (hI K V w Y X hY hX hs.symm).2.2.2.1 0 hXY
  have h2 := (hI K V w X Y hX hY hs).2.2.2.1 0 hYX
  have h3 := idxAt_antisymm w Y X
  simp only [Nat.cast_zero, zero_mul] at h1 h2
  linarith



lemma vAdd_algebraMap_nonneg (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    0 ≤ vAdd w (algebraMap (𝓞 K) K r) := by
  unfold Formalism.BasicNotions.vAdd
  have h1 : w.valuation K (algebraMap (𝓞 K) K r) ≤ 1 := w.valuation_le_one r
  by_cases h0 : w.valuation K (algebraMap (𝓞 K) K r) = 0
  · rw [h0, WithZero.log_zero]
    simp
  · have h2 : WithZero.exp (WithZero.log (w.valuation K (algebraMap (𝓞 K) K r))) ≤ WithZero.exp 0 := by
      rw [WithZero.exp_log h0, WithZero.exp_zero]
      exact h1
    rw [WithZero.exp_le_exp] at h2
    omega




end Gen

section Herm

variable {K : Type} [Field K] [NumberField K] [StarRing K]

lemma exists_rep (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0)
    (φ : Module.Dual K A.V) : ∃ u, h u = φ := by
  classical
  let G : Matrix A.ι A.ι K := fun i j => h (A.b i) (A.b j)
  have hsum : ∀ (c : A.ι → K) (j : A.ι), h (∑ i, star (c i) • A.b i) (A.b j) = Matrix.vecMul c G j := by
    intro c j
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, starRingEnd_apply, star_star,
      smul_eq_mul, Matrix.vecMul, dotProduct, G]
  have key : ∀ c : A.ι → K, Matrix.vecMul c G = 0 → c = 0 := by
    intro c hc
    have hu : h (∑ i, star (c i) • A.b i) = 0 := A.b.ext fun j => by
      rw [hsum c j, hc]
      rfl
    have hu0 := hnd (∑ i, star (c i) • A.b i) (fun y => by rw [hu]; rfl)
    have h0 := (Fintype.linearIndependent_iff.mp A.b.linearIndependent) (fun i => star (c i)) hu0
    funext i
    exact star_eq_zero.mp (h0 i)
  have hinj : Function.Injective (fun c : A.ι → K => Matrix.vecMul c G) := by
    intro c c' hcc
    have := key (c - c') (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.mpr hcc)
    exact sub_eq_zero.mp this
  have hsurj : Function.Surjective (fun c : A.ι → K => Matrix.vecMul c G) :=
    Matrix.vecMul_surjective_iff_isUnit.mpr (Matrix.vecMul_injective_iff_isUnit.mp hinj)
  obtain ⟨c, hc⟩ := hsurj (fun j => φ (A.b j))
  refine ⟨∑ i, star (c i) • A.b i, A.b.ext fun j => ?_⟩
  rw [hsum c j]
  exact congrFun hc j

end Herm

end PI.Dv.ProjGramW
end
end

section
noncomputable section

namespace PI.Dv.ProjGramW

open NumberField IsDedekindDomain Formalism.BasicNotions

section Det

variable {K : Type} [Field K] [NumberField K]

def famC {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V)
    (C : Matrix (Fin d) (Fin d) K) : Fin d → V :=
  fun j => ∑ i, C i j • b i


lemma famC_one {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V) :
    famC b (1 : Matrix (Fin d) (Fin d) K) = b := by
  funext j
  simp [famC, Matrix.one_apply]


variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


lemma idx_self (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {X : Submodule (𝓞 K) V} (hX : X.FG) :
    idxAt w X X = 0 := by
  have hl : LocLe w 0 X X := (locLe_zero_iff w X X).mpr fun x hx =>
    ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rw [one_smul]; exact hx⟩
  exact idx_eq_zero_of_loc hI w hX hX hl hl

lemma idx_add (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {M N P : Submodule (𝓞 K) V}
    (hM : M.FG) (hN : N.FG) (hP : P.FG) (hMN : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hPN : Submodule.span K (P : Set V) = Submodule.span K (N : Set V)) :
    idxAt w M P = idxAt w M N + idxAt w N P :=
  (hI K V w M N hM hN hMN).2.1 P hP hPN

lemma vAdd_mul (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]
  ring

def stdE (d : ℕ) : Fin d → (Fin d →₀ K) := fun k => Finsupp.single k 1


def idxStd (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (C : Matrix (Fin d) (Fin d) K) : ℤ :=
  idxAt w (Submodule.span (𝓞 K) (Set.range (stdE (K := K) d)))
    (Submodule.span (𝓞 K) (Set.range (famC (stdE d) C)))





def colOp {d : ℕ} (j0 : Fin d) (v : Fin d → K) : Matrix (Fin d) (Fin d) K :=
  Matrix.of fun i j => if j = j0 then v i else (if i = j then 1 else 0)

lemma famC_std_apply {d : ℕ} (C : Matrix (Fin d) (Fin d) K) (j i : Fin d) :
    famC (stdE (K := K) d) C j i = C i j := by
  simp [famC, stdE, Finsupp.finsetSum_apply, Finsupp.single_apply]

lemma sum_smul_apply {d : ℕ} (r : Fin d → 𝓞 K) (u : Fin d → (Fin d →₀ K)) (i : Fin d) :
    (∑ k, r k • u k) i = ∑ k, r k • u k i := by
  rw [Finsupp.finsetSum_apply]
  rfl

lemma colOp_col {d : ℕ} (j0 : Fin d) (v : Fin d → K) (k : Fin d) (hk : k ≠ j0) :
    famC (stdE (K := K) d) (colOp j0 v) k = stdE d k := by
  ext i
  rw [famC_std_apply]
  by_cases h : i = k
  · subst h
    simp [colOp, stdE, hk]
  · simp [colOp, stdE, hk, h]

lemma sums_eq {d : ℕ} (j0 : Fin d) (v : Fin d → K) (r : Fin d → 𝓞 K) (hr : r j0 = 0) :
    ∑ k, r k • famC (stdE (K := K) d) (colOp j0 v) k = ∑ k, r k • stdE d k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = j0
  · rw [hk, hr, zero_smul, zero_smul]
  · rw [colOp_col j0 v k hk]



lemma algebraMap_eq_zero {r : 𝓞 K} (h : algebraMap (𝓞 K) K r = 0) : r = 0 :=
  IsFractionRing.injective (𝓞 K) K (by rw [h, map_zero])


lemma span_top_of_mem {Z : Submodule (𝓞 K) K} {z : K} (hz : z ∈ Z) (hz0 : z ≠ 0) :
    Submodule.span K (Z : Set K) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Submodule.subset_span hz) (isUnit_iff_ne_zero.mpr hz0)

lemma one_not_mem (w : HeightOneSpectrum (𝓞 K)) : (1 : 𝓞 K) ∉ w.asIdeal :=
  fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

lemma idx_int (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {y : K} (hy : y ≠ 0) {r : 𝓞 K} (hr : r ≠ 0) :
    idxAt w (Submodule.span (𝓞 K) {y}) (Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r * y}) =
      vAdd w (algebraMap (𝓞 K) K r) := by
  classical
  have hv0 := vAdd_algebraMap_nonneg w r
  set F : ℕ := (vAdd w (algebraMap (𝓞 K) K r)).toNat with hFdef
  have hF : (F : ℤ) = vAdd w (algebraMap (𝓞 K) K r) := Int.toNat_of_nonneg hv0
  have hne := w.intValuation_ne_zero r hr
  have hval : w.intValuation r = WithZero.exp (-(F : ℤ)) := by
    rw [hF]
    unfold vAdd
    rw [HeightOneSpectrum.valuation_of_algebraMap, neg_neg, WithZero.exp_log hne]
  have hmem : r ∈ w.asIdeal ^ F := (w.intValuation_le_pow_iff_mem r F).mp (le_of_eq hval)
  obtain ⟨J, hJ⟩ := (w.intValuation_le_pow_iff_dvd r F).mp (le_of_eq hval)
  have hJw : ¬ J ≤ w.asIdeal := by
    intro hle
    have hd : w.asIdeal ^ (F + 1) ∣ Ideal.span {r} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr hle)
    have := (w.intValuation_le_pow_iff_dvd r (F + 1)).mpr hd
    rw [hval, WithZero.exp_le_exp] at this
    push_cast at this
    linarith
  obtain ⟨t, htJ, htw⟩ := SetLike.not_le_iff_exists.mp hJw
  set X := Submodule.span (𝓞 K) {y} with hX
  set Y := Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r * y} with hY
  set Z := (w.asIdeal ^ F) • X with hZ
  have hry : algebraMap (𝓞 K) K r * y = r • y := (Algebra.smul_def r y).symm
  have hry0 : algebraMap (𝓞 K) K r * y ≠ 0 :=
    mul_ne_zero (fun h => hr (algebraMap_eq_zero h)) hy
  have hyX : y ∈ X := Submodule.mem_span_singleton_self y
  have hryZ : algebraMap (𝓞 K) K r * y ∈ Z := by
    rw [hry]; exact Submodule.smul_mem_smul hmem hyX
  have hXfg : X.FG := Submodule.fg_span (Set.finite_singleton _)
  have hYfg : Y.FG := Submodule.fg_span (Set.finite_singleton _)
  have hZfg : Z.FG := Submodule.FG.of_le hXfg Submodule.smul_le_right
  have hsX : Submodule.span K (X : Set K) = ⊤ := span_top_of_mem hyX hy
  have hsY : Submodule.span K (Y : Set K) = ⊤ := span_top_of_mem (Submodule.mem_span_singleton_self _) hry0
  have hsZ : Submodule.span K (Z : Set K) = ⊤ := span_top_of_mem hryZ hry0
  have hYZ : LocLe w 0 Y Z := by
    rw [locLe_zero_iff]
    intro z hz
    obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨1, one_not_mem w, ?_⟩
    rw [one_smul, hry, smul_smul]
    exact Submodule.smul_mem_smul (Ideal.mul_mem_left _ m hmem) hyX
  have hZY : LocLe w 0 Z Y := by
    rw [locLe_zero_iff]
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Submodule.mem_smul_span_singleton.mp hz
    have hit : i * t ∈ Ideal.span {r} := by rw [hJ]; exact Ideal.mul_mem_mul hi htJ
    obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hit
    refine ⟨t, htw, ?_⟩
    have e : t • i • y = m • (algebraMap (𝓞 K) K r * y) := by
      rw [hry, smul_smul, smul_smul, hm, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ m (Submodule.mem_span_singleton_self _)
  have hrk : Formalism.HN.rkK X = 1 := by
    unfold Formalism.HN.rkK
    rw [hsX, finrank_top, Module.finrank_self]
  have h5 := (hI K K w X X hXfg hXfg rfl).2.2.2.2.1 F
  have hadd := idx_add hI w hXfg hZfg hYfg (hsX.trans hsZ.symm) (hsY.trans hsZ.symm)
  have h0 := idx_eq_zero_of_loc hI w hZfg hYfg hZY hYZ
  rw [hadd, h5, h0, hrk, ← hF]
  simp



lemma colOp_diag {d : ℕ} (k : Fin d) (c : K) :
    colOp k (fun i => if i = k then c else 0) = Matrix.diagonal (fun m => if m = k then c else 1) := by
  ext p q
  simp only [colOp, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hq : q = k
  · subst hq
    by_cases hp : p = q
    · subst hp; simp
    · simp [hp]
  · by_cases hp : p = q
    · subst hp; simp [hq]
    · simp [hp, hq]






end Det


end PI.Dv.ProjGramW
end
end

section
noncomputable section

namespace PI.Dv.ProjGramW

open NumberField IsDedekindDomain Formalism.BasicNotions



end PI.Dv.ProjGramW
end
end
