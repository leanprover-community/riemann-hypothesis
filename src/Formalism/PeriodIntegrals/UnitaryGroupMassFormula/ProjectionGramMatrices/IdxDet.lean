import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionGramMatrices.AlgebraMapNeZeroOfNotMem

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
