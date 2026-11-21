import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEqOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubstInvariants

section
open PowerSeries

namespace GlobalTheory

noncomputable def eigenSeriesCoeff {F : Type} [Field F] (a c : ℕ → F) : ℕ → F
  | 0 => 1
  | k + 1 => (a (k + 1))⁻¹ * ∑ i : Fin (k + 1), c (i + 1) * eigenSeriesCoeff a c (k - i)
decreasing_by omega

theorem eigenSeriesCoeff_succ {F : Type} [Field F] (a c : ℕ → F) (k : ℕ) (ha : a (k + 1) ≠ 0) :
    a (k + 1) * eigenSeriesCoeff a c (k + 1)
      = ∑ i ∈ Finset.range (k + 1), c (i + 1) * eigenSeriesCoeff a c (k - i) := by
  rw [eigenSeriesCoeff, mul_inv_cancel_left₀ ha]
  exact Fin.sum_univ_eq_sum_range (fun i => c (i + 1) * eigenSeriesCoeff a c (k - i)) (k + 1)

theorem exists_rescale_eigen_series_zero {F : Type} [Field F] (p : F⟦X⟧) (χ u : F)
    (hp : constantCoeff p ≠ 0) (hu : u ≠ 0) (hχ : ∀ k : ℕ, 0 < k → χ ^ k ≠ 1) :
    ∃ h : F⟦X⟧, constantCoeff h = 1 ∧
      C u * rescale χ h - h = C ((u - 1) / constantCoeff p) * (p * h) := by
  set L : F := (u - 1) / constantCoeff p with hL
  have hLp : L * coeff 0 p = u - 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, hL]
    field_simp
  refine ⟨PowerSeries.mk (eigenSeriesCoeff (fun k => u * (χ ^ k - 1)) (fun j => L * coeff j p)),
    ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, eigenSeriesCoeff]
  · ext k
    simp only [map_sub, coeff_C_mul, coeff_rescale, coeff_mk]
    rw [coeff_mul]
    simp only [coeff_mk]
    cases k with
    | zero =>
      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, pow_zero]
      rw [eigenSeriesCoeff]
      linear_combination -hLp
    | succ k =>
      have ha : u * (χ ^ (k + 1) - 1) ≠ 0 :=
        mul_ne_zero hu (sub_ne_zero.mpr (hχ (k + 1) (Nat.succ_pos k)))
      have key := eigenSeriesCoeff_succ (fun k => u * (χ ^ k - 1)) (fun j => L * coeff j p) k ha
      simp only [mul_assoc] at key
      rw [← Finset.mul_sum] at key
      rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [Nat.succ_eq_add_one]
      linear_combination key - eigenSeriesCoeff (fun k => u * (χ ^ k - 1))
        (fun j => L * coeff j p) (k + 1) * hLp

theorem exists_rescale_eigen_series : ∀ {F : Type} [Field F] (p : F⟦X⟧) (χ κ : F) (n : ℕ), constantCoeff p ≠ 0 → κ ≠ 0 → χ ≠ 0 → (∀ k : ℕ, 0 < k → χ ^ k ≠ 1) → ∃ h : F⟦X⟧, constantCoeff h = 1 ∧ C κ * rescale χ (X ^ n * h) - X ^ n * h = C ((κ * χ ^ n - 1) / constantCoeff p) * (p * (X ^ n * h)) := by
  intro F _ p χ κ n hp hκ hχ0 hχ
  obtain ⟨h, h0, hh⟩ :=
    exists_rescale_eigen_series_zero p χ (κ * χ ^ n) hp (mul_ne_zero hκ (pow_ne_zero n hχ0)) hχ
  refine ⟨h, h0, ?_⟩
  have hX : rescale χ (X ^ n * h) = C (χ ^ n) * X ^ n * rescale χ h := by
    rw [map_mul, map_pow, rescale_X, mul_pow, map_pow]
  rw [hX]
  calc C κ * (C (χ ^ n) * X ^ n * rescale χ h) - X ^ n * h
      = X ^ n * (C (κ * χ ^ n) * rescale χ h - h) := by rw [map_mul]; ring
    _ = X ^ n * (C ((κ * χ ^ n - 1) / constantCoeff p) * (p * h)) := by rw [hh]
    _ = C ((κ * χ ^ n - 1) / constantCoeff p) * (p * (X ^ n * h)) := by ring

end GlobalTheory
end

section
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen TensorProduct

namespace GlobalTheory.TruncDiag

theorem exists_comb {S : Type} [CommRing S] (h : ℕ → S⟦X⟧) (hh : ∀ n, IsUnit (h n)) (m : ℕ) (y : S⟦X⟧) :
    ∃ c : ℕ → S, (X : S⟦X⟧) ^ m ∣ y - ∑ n ∈ Finset.range m, c n • (X ^ n * h n) := by
  induction m with
  | zero => exact ⟨fun _ => 0, by simp⟩
  | succ m ih =>
    obtain ⟨c, z, hz⟩ := ih
    have hu : IsUnit (constantCoeff (h m)) := (hh m).map constantCoeff
    refine ⟨fun n => if n = m then constantCoeff z * ↑hu.unit⁻¹ else c n, ?_⟩
    rw [Finset.sum_range_succ]
    beta_reduce
    rw [if_pos rfl]
    have hsum : ∑ n ∈ Finset.range m,
        (if n = m then constantCoeff z * ↑hu.unit⁻¹ else c n) • ((X : S⟦X⟧) ^ n * h n)
          = ∑ n ∈ Finset.range m, c n • ((X : S⟦X⟧) ^ n * h n) :=
      Finset.sum_congr rfl fun n hn => by rw [if_neg (Finset.mem_range.mp hn).ne]
    rw [hsum]
    have hX : (X : S⟦X⟧) ∣ z - (constantCoeff z * ↑hu.unit⁻¹) • h m := by
      rw [X_dvd_iff, smul_eq_C_mul, map_sub, map_mul, constantCoeff_C, mul_assoc,
        IsUnit.val_inv_mul, mul_one, sub_self]
    obtain ⟨d, hd⟩ := hX
    refine ⟨d, ?_⟩
    simp only [smul_eq_C_mul] at hz hd ⊢
    linear_combination hz + (X : S⟦X⟧) ^ m * hd

theorem mem_of_gens {S : Type} [CommRing S] {r : ℕ} (m : ℕ) (h : Fin r → ℕ → S⟦X⟧) (hh : ∀ k n, IsUnit (h k n))
    (N : Submodule S (Fin r → S⟦X⟧)) (h0 : ∀ y : Fin r → S⟦X⟧, (∀ k, (X : S⟦X⟧) ^ m ∣ y k) → y ∈ N)
    (h1 : ∀ k n, n < m → (Pi.single k (X ^ n * h k n) : Fin r → S⟦X⟧) ∈ N) (y : Fin r → S⟦X⟧) : y ∈ N := by
  classical
  have key : ∀ k, (Pi.single k (y k) : Fin r → S⟦X⟧) ∈ N := by
    intro k
    obtain ⟨c, hc⟩ := exists_comb (h k) (hh k) m (y k)
    have hmem : (Pi.single k (y k) : Fin r → S⟦X⟧)
        - ∑ n ∈ Finset.range m, c n • (Pi.single k ((X : S⟦X⟧) ^ n * h k n) : Fin r → S⟦X⟧) ∈ N := by
      apply h0
      intro j
      by_cases hj : j = k
      · subst hj
        simpa [Finset.sum_apply] using hc
      · simp [Finset.sum_apply, Pi.single_eq_of_ne hj]
    have hsum : ∑ n ∈ Finset.range m, c n • (Pi.single k ((X : S⟦X⟧) ^ n * h k n) : Fin r → S⟦X⟧) ∈ N :=
      N.sum_mem fun n hn => N.smul_mem _ (h1 k n (Finset.mem_range.mp hn))
    simpa using N.add_mem hmem hsum
  rw [← Finset.univ_sum_single y]
  exact N.sum_mem fun k _ => key k

theorem pow_dvd_of_map {O F : Type} [CommRing O] [Field F] [Algebra O F] (Λ : O⟦X⟧ →ₐ[O] F⟦X⟧) (η : F⟦X⟧)
    (hinj : Function.Injective (algebraMap O F)) (hX : Λ X = X * η) (hη : IsUnit η) (m : ℕ) (c : O⟦X⟧)
    (hc : (X : F⟦X⟧) ^ m ∣ Λ c) : (X : O⟦X⟧) ^ m ∣ c := by
  have hcc : ∀ d : O⟦X⟧, constantCoeff (Λ d) = algebraMap O F (constantCoeff d) := by
    intro d
    obtain ⟨e, he⟩ : (X : O⟦X⟧) ∣ d - C (constantCoeff d) := by
      rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
    have hd : d = C (constantCoeff d) + X * e := by rw [← he]; ring
    have hC : Λ (C (constantCoeff d)) = C (algebraMap O F (constantCoeff d)) := by
      have h1 : (C (constantCoeff d) : O⟦X⟧) = algebraMap O O⟦X⟧ (constantCoeff d) := by
        rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [h1, AlgHom.commutes, PowerSeries.algebraMap_apply]
    conv_lhs => rw [hd]
    rw [map_add, map_mul, hC, hX, map_add, constantCoeff_C, map_mul, map_mul, constantCoeff_X,
      zero_mul, zero_mul, add_zero]
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    have h0 : constantCoeff c = 0 := by
      apply hinj
      rw [← hcc, map_zero]
      exact X_dvd_iff.mp (dvd_trans (dvd_pow_self X (Nat.succ_ne_zero m)) hc)
    obtain ⟨d, rfl⟩ := X_dvd_iff.mpr h0
    rw [map_mul, hX, pow_succ', mul_assoc] at hc
    have hc' : (X : F⟦X⟧) ^ m ∣ Λ d :=
      hη.dvd_mul_left.mp ((mul_dvd_mul_iff_left (X_ne_zero (R := F))).mp hc)
    rw [pow_succ']
    exact mul_dvd_mul_left X (ih d hc')

theorem map_pow_dvd {O F : Type} [CommRing O] [Field F] [Algebra O F] (Λ : O⟦X⟧ →ₐ[O] F⟦X⟧) (η : F⟦X⟧)
    (hX : Λ X = X * η) (m : ℕ) (c : O⟦X⟧) (hc : (X : O⟦X⟧) ^ m ∣ c) : (X : F⟦X⟧) ^ m ∣ Λ c := by
  obtain ⟨d, rfl⟩ := hc
  rw [map_mul, map_pow, hX, mul_pow, mul_assoc]
  exact dvd_mul_right _ _

theorem mulVec_dvd {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (a : R) (y : Fin r → R)
    (hy : ∀ k, a ∣ y k) (u : Fin r) : a ∣ M.mulVec y u := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (hy k) _

theorem rescale_dvd {F : Type} [Field F] (χ : F) (m : ℕ) (y : F⟦X⟧) (hy : (X : F⟦X⟧) ^ m ∣ y) :
    (X : F⟦X⟧) ^ m ∣ rescale χ y := by
  obtain ⟨d, rfl⟩ := hy
  exact ⟨C χ ^ m * rescale χ d, by rw [map_mul, map_pow, rescale_X]; ring⟩

def tr (F : Type) [Field F] (r m : ℕ) : (Fin r → F⟦X⟧) →ₗ[F] (Fin r × Fin m → F) :=
  LinearMap.pi fun x => (coeff (x.2 : ℕ)) ∘ₗ LinearMap.proj x.1

theorem tr_eq_zero {F : Type} [Field F] {r m : ℕ} (y : Fin r → F⟦X⟧) :
    tr F r m y = 0 ↔ ∀ k, (X : F⟦X⟧) ^ m ∣ y k := by
  constructor
  · intro h k
    rw [X_pow_dvd_iff]
    intro n hn
    have := congrFun h (k, ⟨n, hn⟩)
    simpa [tr] using this
  · intro h
    funext x
    simpa [tr] using X_pow_dvd_iff.mp (h x.1) x.2 x.2.isLt

theorem tr_surjective (F : Type) [Field F] (r m : ℕ) : Function.Surjective (tr F r m) := by
  intro w
  refine ⟨fun k => PowerSeries.mk fun n => if hn : n < m then w (k, ⟨n, hn⟩) else 0, ?_⟩
  funext x
  simp [tr, coeff_mk, x.2.isLt]

def opD {F : Type} [Field F] {r : ℕ} (p : F⟦X⟧) (χ : F) (κ : Fin r → F) :
    (Fin r → F⟦X⟧) →ₗ[F] (Fin r → F⟦X⟧) where
  toFun y := fun u => p⁻¹ * (C (κ u) * rescale χ (y u) - y u)
  map_add' y z := by funext u; simp only [Pi.add_apply, map_add]; ring
  map_smul' a y := by
    funext u
    have : rescale χ (C a : F⟦X⟧) = C a := by
      ext n; simp only [coeff_rescale, coeff_C]; split_ifs with h <;> simp [h]
    simp only [Pi.smul_apply, smul_eq_C_mul, map_mul, this, RingHom.id_apply]; ring

theorem tr_opD_congr {F : Type} [Field F] {r m : ℕ} (p : F⟦X⟧) (χ : F) (κ : Fin r → F) (y z : Fin r → F⟦X⟧)
    (h : tr F r m y = tr F r m z) : tr F r m (opD p χ κ y) = tr F r m (opD p χ κ z) := by
  have h' : tr F r m (y - z) = 0 := by rw [map_sub, h, sub_self]
  rw [tr_eq_zero] at h'
  rw [← sub_eq_zero, ← map_sub, ← map_sub, tr_eq_zero]
  intro u
  show (X : F⟦X⟧) ^ m ∣ p⁻¹ * (C (κ u) * rescale χ ((y - z) u) - (y - z) u)
  exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right (rescale_dvd χ m _ (h' u)) _) (h' u)) _

theorem injective_of_span {F Q W ι : Type} [Field F] [AddCommGroup Q] [Module F Q] [AddCommGroup W] [Module F W]
    [Fintype ι] (hW : Module.finrank F W = Fintype.card ι) (Ψ : Q →ₗ[F] W) (g : ι → Q)
    (hg : Submodule.span F (Set.range g) = ⊤) (hΨ : Function.Surjective Ψ) : Function.Injective Ψ := by
  have hQ : Module.Finite F Q := ⟨by rw [← hg]; exact Submodule.fg_span (Set.finite_range g)⟩
  have hWf : Module.Finite F W := Module.Finite.of_surjective Ψ hΨ
  have h1 : Module.finrank F Q ≤ Fintype.card ι := by
    have := finrank_range_le_card (R := F) g
    simp only [Set.finrank] at this
    rw [hg, finrank_top] at this
    exact this
  have h2 : Module.finrank F W ≤ Module.finrank F Q := by
    have := LinearMap.finrank_range_le Ψ
    rwa [LinearMap.range_eq_top.mpr hΨ, finrank_top] at this
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by omega)).mpr hΨ

theorem diag_of_model {F Q : Type} [Field F] [AddCommGroup Q] [Module F Q] (r m : ℕ) (p : F⟦X⟧) (χ : F)
    (κ : Fin r → F) (hp : constantCoeff p ≠ 0) (hχ0 : χ ≠ 0) (hχ : ∀ k : ℕ, 0 < k → χ ^ k ≠ 1)
    (hκ : ∀ u, κ u ≠ 0) (f : Q →ₗ[F] Q) (Ψ : Q →ₗ[F] (Fin r × Fin m → F)) (hΨ : Function.Bijective Ψ)
    (hI : ∀ q, ∃ y, Ψ q = tr F r m y ∧ Ψ (f q) = tr F r m (opD p χ κ y)) :
    DiagWith f ((Finset.univ : Finset (Fin r × Fin m)).val.map
      fun x => (κ x.1 * χ ^ (x.2 : ℕ) - 1) / constantCoeff p) := by
  classical
  choose hs hs0 hseq using fun (u : Fin r) (n : ℕ) =>
    GlobalTheory.exists_rescale_eigen_series p χ (κ u) n hp (hκ u) hχ0 hχ
  have hsu : ∀ u n, IsUnit (hs u n) := fun u n => by
    rw [isUnit_iff_constantCoeff, hs0]; exact isUnit_one
  obtain ⟨ys, hys⟩ : ∃ ys : Fin r × Fin m → (Fin r → F⟦X⟧),
      ys = fun x => Pi.single x.1 ((X : F⟦X⟧) ^ (x.2 : ℕ) * hs x.1 x.2) := ⟨_, rfl⟩
  have hopD : ∀ x, opD p χ κ (ys x) = ((κ x.1 * χ ^ (x.2 : ℕ) - 1) / constantCoeff p) • ys x := by
    intro x
    funext v
    show p⁻¹ * (C (κ v) * rescale χ (ys x v) - ys x v)
      = ((κ x.1 * χ ^ (x.2 : ℕ) - 1) / constantCoeff p) • ys x v
    rw [hys]
    by_cases hv : v = x.1
    · subst hv
      simp only [Pi.single_eq_same]
      rw [hseq, smul_eq_C_mul]
      linear_combination (C ((κ x.1 * χ ^ (x.2 : ℕ) - 1) / constantCoeff p) *
        ((X : F⟦X⟧) ^ (x.2 : ℕ) * hs x.1 x.2)) * PowerSeries.inv_mul_cancel p hp
    · simp only [Pi.single_eq_of_ne hv, map_zero, mul_zero, sub_zero, smul_zero]
  have hspan : ⊤ ≤ Submodule.span F (Set.range fun x => tr F r m (ys x)) := by
    intro t _
    obtain ⟨y, rfl⟩ := tr_surjective F r m t
    refine mem_of_gens (S := F) m hs hsu
      ((Submodule.span F (Set.range fun x => tr F r m (ys x))).comap (tr F r m)) ?_ ?_ y
    · intro y hy
      rw [Submodule.mem_comap, (tr_eq_zero y).mpr hy]
      exact Submodule.zero_mem _
    · intro k n hn
      rw [Submodule.mem_comap]
      exact Submodule.subset_span ⟨(k, ⟨n, hn⟩), by rw [hys]⟩
  have hcard : Fintype.card (Fin r × Fin m) = Module.finrank F (Fin r × Fin m → F) :=
    (Module.finrank_fintype_fun_eq_card F).symm
  obtain ⟨bW, hbW⟩ : ∃ bW : Module.Basis (Fin r × Fin m) F (Fin r × Fin m → F),
      ⇑bW = fun x => tr F r m (ys x) :=
    ⟨basisOfTopLeSpanOfCardEqFinrank _ hspan hcard, coe_basisOfTopLeSpanOfCardEqFinrank _ _ _⟩
  obtain ⟨Ψe, hΨe⟩ : ∃ Ψe : Q ≃ₗ[F] (Fin r × Fin m → F), ⇑Ψe = ⇑Ψ :=
    ⟨LinearEquiv.ofBijective Ψ hΨ, rfl⟩
  refine ⟨r * m, (bW.map Ψe.symm).reindex finProdFinEquiv,
    fun j => (κ (finProdFinEquiv.symm j).1 * χ ^ ((finProdFinEquiv.symm j).2 : ℕ) - 1) / constantCoeff p,
    ?_, ?_⟩
  · intro j
    simp only [Module.Basis.reindex_apply, Module.Basis.map_apply, hbW]
    apply hΨ.1
    obtain ⟨y, hy1, hy2⟩ := hI (Ψe.symm (tr F r m (ys (finProdFinEquiv.symm j))))
    have hq : Ψ (Ψe.symm (tr F r m (ys (finProdFinEquiv.symm j))))
        = tr F r m (ys (finProdFinEquiv.symm j)) := by
      rw [← hΨe]; exact Ψe.apply_symm_apply _
    rw [hy2, map_smul, hq, tr_opD_congr p χ κ y _ (hy1.symm.trans hq), hopD, map_smul]
  · have he : (Finset.univ : Finset (Fin (r * m))).val.map finProdFinEquiv.symm
        = (Finset.univ : Finset (Fin r × Fin m)).val := by
      exact Multiset.map_univ_val_equiv (finProdFinEquiv (m := r) (n := m)).symm
    rw [← he, Multiset.map_map]
    rfl

theorem diagWith_trunc : ∀ {O F P : Type} [CommRing O] [Field F] [Algebra O F] [AddCommGroup P] [Module O P] (P' : Submodule O P) (r m : ℕ) (θ : (Fin r → O⟦X⟧) ≃ₗ[O] P) (Λ : O⟦X⟧ →ₐ[O] F⟦X⟧) (η p : F⟦X⟧) (M : Matrix (Fin r) (Fin r) F⟦X⟧) (χ : F) (κ : Fin r → F) (nb : P →ₗ[O] P), Function.Injective (algebraMap O F) → (∀ c, θ c ∈ P' ↔ ∀ k, (X : O⟦X⟧) ^ m ∣ c k) → Λ X = X * η → IsUnit η → IsUnit M.det → constantCoeff p ≠ 0 → χ ≠ 0 → (∀ k : ℕ, 0 < k → χ ^ k ≠ 1) → (∀ u, κ u ≠ 0) → (∀ c c', nb (θ c) = θ c' → ∀ u, p * M.mulVec (fun k => Λ (c' k)) u = C (κ u) * rescale χ (M.mulVec (fun k => Λ (c k)) u) - M.mulVec (fun k => Λ (c k)) u) → ∃ hs : P' ≤ P'.comap nb, DiagWith ((Submodule.mapQ P' P' nb hs).baseChange F) ((Finset.univ : Finset (Fin r × Fin m)).val.map fun x => (κ x.1 * χ ^ (x.2 : ℕ) - 1) / constantCoeff p) := by
  intro O F P _ _ _ _ _ P' r m θ Λ η p M χ κ nb hinj hP' hX hη hM hp hχ0 hχ hκ hnb
  classical
  have hsolve : ∀ c c', nb (θ c) = θ c' →
      M.mulVec (fun k => Λ (c' k)) = opD p χ κ (M.mulVec (fun k => Λ (c k))) := by
    intro c c' hcc
    funext u
    show _ = p⁻¹ * (C (κ u) * rescale χ (M.mulVec (fun k => Λ (c k)) u) - M.mulVec (fun k => Λ (c k)) u)
    rw [← hnb c c' hcc u, ← mul_assoc, PowerSeries.inv_mul_cancel p hp, one_mul]
  have hdiv : ∀ c : Fin r → O⟦X⟧, (∀ k, (X : O⟦X⟧) ^ m ∣ c k) →
      ∀ u, (X : F⟦X⟧) ^ m ∣ M.mulVec (fun k => Λ (c k)) u := fun c hc =>
    mulVec_dvd M _ _ fun k => map_pow_dvd Λ η hX m (c k) (hc k)
  have hs : P' ≤ P'.comap nb := by
    intro x hx
    rw [Submodule.mem_comap]
    obtain ⟨c, rfl⟩ := θ.surjective x
    have hcc : nb (θ c) = θ (θ.symm (nb (θ c))) := (θ.apply_symm_apply _).symm
    rw [hcc, hP']
    have hdc := (hP' c).mp hx
    have h1 : ∀ u, (X : F⟦X⟧) ^ m ∣ M.mulVec (fun k => Λ (θ.symm (nb (θ c)) k)) u := by
      intro u
      rw [hsolve c _ hcc]
      exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right
        (rescale_dvd χ m _ (hdiv c hdc u)) _) (hdiv c hdc u)) _
    intro k
    apply pow_dvd_of_map Λ η hinj hX hη m
    have h2 := mulVec_dvd M⁻¹ _ _ h1 k
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM, Matrix.one_mulVec] at h2
  refine ⟨hs, ?_⟩
  have hΛs : ∀ (a : O) (c : O⟦X⟧), Λ (a • c) = algebraMap O F a • Λ c := by
    intro a c
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, PowerSeries.algebraMap_apply, smul_eq_C_mul]
  obtain ⟨L, hL⟩ : ∃ L : (Fin r → F⟦X⟧) →ₗ[F] (Fin r × Fin m → F),
      ∀ y, L y = tr F r m (M.mulVec y) :=
    ⟨{ toFun := fun y => tr F r m (M.mulVec y)
       map_add' := fun y z => by simp only [Matrix.mulVec_add, map_add]
       map_smul' := fun b y => by simp only [Matrix.mulVec_smul, map_smul, RingHom.id_apply] },
     fun _ => rfl⟩
  obtain ⟨Ψ0, hΨ0⟩ : ∃ Ψ0 : P →ₗ[O] (Fin r × Fin m → F),
      ∀ x, Ψ0 x = L (fun k => Λ (θ.symm x k)) :=
    ⟨{ toFun := fun x => L (fun k => Λ (θ.symm x k))
       map_add' := fun x y => by
         simp only [map_add, Pi.add_apply]
         rw [← map_add]
         rfl
       map_smul' := fun a x => by
         simp only [RingHom.id_apply]
         have : (fun k => Λ (θ.symm (a • x) k)) = algebraMap O F a • (fun k => Λ (θ.symm x k)) := by
           funext k
           rw [map_smul, Pi.smul_apply, hΛs, Pi.smul_apply]
         rw [this, map_smul, algebraMap_smul] },
     fun _ => rfl⟩
  have hker : P' ≤ LinearMap.ker Ψ0 := by
    intro x hx
    rw [LinearMap.mem_ker]
    obtain ⟨c, rfl⟩ := θ.surjective x
    rw [hΨ0, hL, LinearEquiv.symm_apply_apply, tr_eq_zero]
    exact hdiv c ((hP' c).mp hx)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : F ⊗[O] (P ⧸ P') →ₗ[F] (Fin r × Fin m → F),
      ∀ (a : F) (x : P), Ψ (a ⊗ₜ Submodule.Quotient.mk x) = a • Ψ0 x :=
    ⟨(P'.liftQ Ψ0 hker).liftBaseChange F, fun a x => by
      rw [LinearMap.liftBaseChange_tmul, Submodule.liftQ_apply]⟩
  have hsurj : Function.Surjective Ψ := by
    intro t
    have hN : ∀ y : Fin r → F⟦X⟧, L y ∈ LinearMap.range Ψ := fun y =>
      mem_of_gens (S := F) m (fun _ n => η ^ n) (fun _ n => hη.pow n)
        ((LinearMap.range Ψ).comap L)
        (fun y hy => by
          rw [Submodule.mem_comap, hL, (tr_eq_zero _).mpr (mulVec_dvd M _ _ hy)]
          exact Submodule.zero_mem _)
        (fun k n _ => by
          rw [Submodule.mem_comap, LinearMap.mem_range]
          refine ⟨1 ⊗ₜ Submodule.Quotient.mk (θ (Pi.single k ((X : O⟦X⟧) ^ n))), ?_⟩
          rw [hΨ, one_smul, hΨ0, LinearEquiv.symm_apply_apply]
          congr 1
          funext j
          by_cases hj : j = k
          · subst hj
            simp [map_pow, hX, mul_pow]
          · simp [Pi.single_eq_of_ne hj])
        y
    obtain ⟨y, rfl⟩ := tr_surjective F r m t
    obtain ⟨q, hq⟩ := LinearMap.mem_range.mp (hN (M⁻¹.mulVec y))
    refine ⟨q, ?_⟩
    rw [hq, hL, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec]
  obtain ⟨g0, hg0⟩ : ∃ g0 : Fin r × Fin m → P ⧸ P',
      g0 = fun x => Submodule.Quotient.mk (θ (Pi.single x.1 ((X : O⟦X⟧) ^ (x.2 : ℕ)))) := ⟨_, rfl⟩
  have hspanO : ∀ z : P ⧸ P', z ∈ Submodule.span O (Set.range g0) := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P' z
    obtain ⟨c, rfl⟩ := θ.surjective x
    exact mem_of_gens (S := O) m (fun _ _ => 1) (fun _ _ => isUnit_one)
      ((Submodule.span O (Set.range g0)).comap (P'.mkQ ∘ₗ θ.toLinearMap))
      (fun y hy => by
        rw [Submodule.mem_comap, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero P').mpr ((hP' y).mpr hy)]
        exact Submodule.zero_mem _)
      (fun k n hn => by
        rw [Submodule.mem_comap]
        exact Submodule.subset_span ⟨(k, ⟨n, hn⟩), by rw [hg0]; simp⟩)
      c
  have hspanF : Submodule.span F (Set.range fun x => (1 : F) ⊗ₜ[O] g0 x) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    induction q using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul a z =>
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp (hspanO z)
      rw [← hc, TensorProduct.tmul_sum]
      refine Submodule.sum_mem _ fun x _ => ?_
      have : a ⊗ₜ[O] (c x • g0 x) = (c x • a) • ((1 : F) ⊗ₜ[O] g0 x) := by
        rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)
  have hinjΨ : Function.Injective Ψ :=
    injective_of_span (ι := Fin r × Fin m) (Module.finrank_fintype_fun_eq_card F) Ψ _ hspanF hsurj
  have hI : ∀ q, ∃ y, Ψ q = tr F r m y ∧
      Ψ (((Submodule.mapQ P' P' nb hs).baseChange F) q) = tr F r m (opD p χ κ y) := by
    intro q
    induction q using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul a z =>
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P' z
      obtain ⟨c, rfl⟩ := θ.surjective x
      refine ⟨a • M.mulVec (fun k => Λ (c k)), ?_, ?_⟩
      · rw [hΨ, hΨ0, hL, LinearEquiv.symm_apply_apply, map_smul]
      · rw [LinearMap.baseChange_tmul, Submodule.mapQ_apply, hΨ, hΨ0, hL,
          hsolve c _ (θ.apply_symm_apply _).symm, map_smul, map_smul]
    | add x y hx hy =>
      obtain ⟨y1, h1, h2⟩ := hx
      obtain ⟨y2, h3, h4⟩ := hy
      exact ⟨y1 + y2, by rw [map_add, h1, h3, map_add],
        by rw [map_add, map_add, h2, h4, map_add, map_add]⟩
  exact diag_of_model r m p χ κ hp hχ0 hχ hκ _ Ψ ⟨hinjΨ, hsurj⟩ hI

end GlobalTheory.TruncDiag
end
end

section
noncomputable section

namespace GlobalTheory.SenLines

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen TensorProduct
open GlobalTheory.WachTie.MatF

section Algebra

theorem quot_equiv {O P : Type} [CommRing O] [AddCommGroup P] [Module O P] (P' : Submodule O P) {r : ℕ} (m : ℕ)
    (θ : (Fin r → O⟦X⟧) ≃ₗ[O] P) (h : ∀ c, θ c ∈ P' ↔ ∀ k, (X : O⟦X⟧) ^ m ∣ c k) :
    Nonempty ((P ⧸ P') ≃ₗ[O] (Fin m × Fin r → O)) := by
  let tr : (Fin r → O⟦X⟧) →ₗ[O] (Fin m × Fin r → O) :=
    LinearMap.pi fun x => (coeff (x.1 : ℕ)).comp (LinearMap.proj x.2)
  let f : P →ₗ[O] (Fin m × Fin r → O) := tr.comp θ.symm.toLinearMap
  have hs : Function.Surjective f := by
    intro y
    refine ⟨θ fun k => PowerSeries.mk fun a => if ha : a < m then y (⟨a, ha⟩, k) else 0, ?_⟩
    funext x
    simp [f, tr]
  have hk : P' = LinearMap.ker f := by
    ext x
    obtain ⟨c, rfl⟩ := θ.surjective x
    rw [h, LinearMap.mem_ker, funext_iff]
    simp only [X_pow_dvd_iff, f, tr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.pi_apply, LinearMap.proj_apply, Pi.zero_apply]
    exact ⟨fun H x => H x.2 x.1 x.1.2, fun H k a ha => H (⟨a, ha⟩, k)⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hs)⟩

theorem charpoly_of_diagWith {F M : Type} [Field F] [AddCommGroup M] [Module F M] [Module.Finite F M]
    (f : M →ₗ[F] M) (S : Multiset F) (h : DiagWith f S) :
    f.charpoly = (S.map fun s => Polynomial.X - Polynomial.C s).prod := by
  obtain ⟨m, b, e, he, rfl⟩ := h
  have hm : LinearMap.toMatrix b b f = Matrix.diagonal e := by
    ext a c
    rw [LinearMap.toMatrix_apply, he, map_smul, b.repr_self, Matrix.diagonal_apply]
    by_cases hac : a = c
    · subst hac; simp
    · simp [hac, Finsupp.single_eq_of_ne hac]
  rw [← LinearMap.charpoly_toMatrix f b, hm, Matrix.charpoly_diagonal, Multiset.map_map]
  rfl

theorem eigWith_of_diagWith {O F k Q : Type} [CommRing O] [Field F] [Field k] [Algebra O F] [Algebra O k]
    [AddCommGroup Q] [Module O Q] [Module.Free O Q] [Module.Finite O Q]
    (hinj : Function.Injective (algebraMap O F)) (f : Q →ₗ[O] Q) (S : Multiset O)
    (h : DiagWith (f.baseChange F) (S.map (algebraMap O F))) :
    EigWith (f.baseChange k) (S.map (algebraMap O k)) := by
  have h1 := charpoly_of_diagWith _ _ h
  have key : ∀ (E : Type) [Field E] [Algebra O E],
      ((S.map (algebraMap O E)).map fun s => Polynomial.X - Polynomial.C s).prod =
        (S.map fun s => Polynomial.X - Polynomial.C s).prod.map (algebraMap O E) := by
    intro E _ _
    rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 2
    funext s
    simp
  rw [key, LinearMap.charpoly_baseChange] at h1
  refine ⟨inferInstance, ?_⟩
  rw [key, LinearMap.charpoly_baseChange, Polynomial.map_injective _ hinj h1]

theorem exists_cc {O F : Type} [CommRing O] [Field F] [CharZero F] [Algebra O F] (l : ℕ) (hl : l ≠ 0)
    (hu : IsUnit (1 + (l : O))) (a : ℤ) :
    ∃ c : O, algebraMap O F c = ((cc l a : ℚ) : F) ∧ (l : O) ∣ c + a := by
  have hl' : (l : F) ≠ 0 := Nat.cast_ne_zero.2 hl
  have h1 : (1 + (l : F)) ≠ 0 := by exact_mod_cast (by omega : 1 + l ≠ 0)
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have hw' : algebraMap O F w = (1 + (l : F))⁻¹ := by
    have := congrArg (algebraMap O F) hw
    rw [map_mul, map_add, map_one, map_natCast] at this
    exact (eq_inv_of_mul_eq_one_right this)
  induction a using Int.induction_on with
  | zero => exact ⟨0, by simp [cc], by simp⟩
  | succ a ih =>
    obtain ⟨c, hc, d, hd⟩ := ih
    refine ⟨(1 + l) * c - 1, ?_, d + c, ?_⟩
    · rw [map_sub, map_mul, hc]
      simp only [cc, map_add, map_one, map_natCast]
      push_cast
      rw [zpow_add_one₀ h1]
      field_simp
      ring
    · push_cast at hd ⊢
      linear_combination hd
  | pred a ih =>
    obtain ⟨c, hc, d, hd⟩ := ih
    refine ⟨(c + 1) * w, ?_, d - (c + 1) * w, ?_⟩
    · rw [map_mul, map_add, hc, hw']
      simp only [cc, map_one]
      push_cast
      rw [zpow_sub_one₀ h1]
      field_simp
      ring
    · push_cast at hd ⊢
      linear_combination hd + (c + 1) * hw

theorem exists_factor {O P D : Type} [CommRing O] [AddCommGroup P] [Module O P] [AddCommGroup D] [Module O D]
    (f g : P →ₗ[O] D) (hf : Function.Injective f) (h : ∀ x, ∃ y, f y = g x) :
    ∃ nb : P →ₗ[O] P, ∀ x, f (nb x) = g x := by
  refine ⟨(LinearEquiv.ofInjective f hf).symm.toLinearMap.comp (g.codRestrict (LinearMap.range f) h),
    fun x => ?_⟩
  have := (LinearEquiv.ofInjective f hf).apply_symm_apply (g.codRestrict (LinearMap.range f) h x)
  exact congrArg Subtype.val this

theorem dvd_zpow_sub_one {R : Type} [CommRing R] (x : R) (s : Rˣ) (h : x ∣ (s : R) - 1) (j : ℤ) :
    x ∣ ((s ^ j : Rˣ) : R) - 1 := by
  have key : ∀ t : Rˣ, x ∣ (t : R) - 1 ↔
      Units.map (Ideal.Quotient.mk (Ideal.span {x})).toMonoidHom t = 1 := fun t => by
    rw [Units.ext_iff, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
    simp
  rw [key] at h ⊢
  rw [map_zpow, h, one_zpow]

end Algebra

section Series

theorem exists_mu {F : Type} [Field F] (χ : F) (hχ : χ ≠ 0) (η m S A : (F⟦X⟧)ˣ) (j w : ℤ)
    (h1 : (η : F⟦X⟧) * S = C χ * rescale χ (η : F⟦X⟧))
    (h2 : (A : F⟦X⟧) * m = C (χ ^ (-w)) * rescale χ (m : F⟦X⟧)) :
    ∃ μ : (F⟦X⟧)ˣ, ((S ^ j : (F⟦X⟧)ˣ) : F⟦X⟧) * μ = C (χ ^ (j + w)) * A * rescale χ (μ : F⟦X⟧) := by
  let R : (F⟦X⟧)ˣ →* (F⟦X⟧)ˣ := Units.map (rescale χ).toMonoidHom
  let c : (F⟦X⟧)ˣ := Units.map (C : F →+* F⟦X⟧).toMonoidHom (Units.mk0 χ hχ)
  have hc : ∀ k : ℤ, ((c ^ k : (F⟦X⟧)ˣ) : F⟦X⟧) = C (χ ^ k) := fun k => by
    rw [← map_zpow]
    change C (((Units.mk0 χ hχ) ^ k : Fˣ) : F) = _
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have e1 : η * S = c * R η := Units.ext h1
  have e2 : A * m = c ^ (-w) * R m := Units.ext (by rw [Units.val_mul, Units.val_mul, hc]; exact h2)
  have e3 : S ^ j * (η ^ j * m⁻¹) = c ^ (j + w) * A * R (η ^ j * m⁻¹) := by
    rw [← mul_assoc, ← mul_zpow, mul_comm S, e1, eq_mul_inv_of_mul_eq e2, map_mul, map_zpow, map_inv,
      mul_zpow, zpow_add, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  refine ⟨η ^ j * m⁻¹, ?_⟩
  have := congrArg Units.val e3
  rw [Units.val_mul, Units.val_mul (c ^ (j + w) * A), Units.val_mul (c ^ (j + w)), hc] at this
  exact this

theorem eigMs_eq {F : Type} [Field F] [CharZero F] (l : ℕ) {r : ℕ} (u : Fin r → ℤ) (w j j' : ℤ) :
    eigMs F l (Finset.univ.val.map u) w j j' =
      (Finset.univ : Finset (Fin r × Fin (j' - j).toNat)).val.map fun x =>
        ((1 + (l : F)) ^ (j + w - u x.1) * (1 + (l : F)) ^ (x.2 : ℕ) - 1) / (-(l : F)) := by
  have h1 : (1 + (l : F)) ≠ 0 := by exact_mod_cast (by omega : 1 + l ≠ 0)
  rw [← Finset.univ_product_univ, Finset.product_val, eigMs, Multiset.bind_map]
  rw [show ∀ (s : Multiset (Fin r)) (t : Multiset (Fin (j' - j).toNat)),
    s ×ˢ t = s.bind fun a => t.map (Prod.mk a) from fun _ _ => rfl, Multiset.map_bind]
  refine Multiset.bind_congr fun k _ => ?_
  rw [Int.Ico_eq_finset_map, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_univ]
  simp only [Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [cc, Function.comp, Function.Embedding.trans_apply, Fin.valEmbedding_apply,
    Nat.castEmbedding_apply, addLeftEmbedding_apply]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ h1]
  congr 3
  ring

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (J : O⟦X⟧ →ₐ[O] O⟦X⟧) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n)

def th : (Fin r → O⟦X⟧) →ₗ[O] W.DD T where
  toFun c := ∑ k, (Pi.single i (J (c k)) : LetA O n) • (b k : W.DD T)
  map_add' c d := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.add_apply, map_add, Pi.single_add, add_smul]
  map_smul' c d := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, map_smul, Pi.single_smul, smul_assoc]

theorem th_apply (c : Fin r → O⟦X⟧) :
    th W T J b i c = ∑ k, (Pi.single i (J (c k)) : LetA O n) • (b k : W.DD T) := rfl

theorem mul_single (a : LetA O n) (x : O⟦X⟧) : a * Pi.single i x = Pi.single i (a i * x) := by
  funext m
  by_cases h : m = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem smul_th_eq (a : LetA O n) (c : Fin r → O⟦X⟧) :
    a • th W T J b i c = ∑ k, (Pi.single i (a i * J (c k)) : LetA O n) • (b k : W.DD T) := by
  rw [th_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, mul_single]

theorem smul_th {a : LetA O n} {e : O⟦X⟧} (h : a i = J e) (c : Fin r → O⟦X⟧) :
    a • th W T J b i c = th W T J b i (e • c) := by
  rw [smul_th_eq, th_apply]
  simp only [h, Pi.smul_apply, smul_eq_mul, map_mul]

theorem th_coord {c : Fin r → O⟦X⟧} {a : Fin r → LetA O n}
    (h : th W T J b i c = ∑ k, a k • (b k : W.DD T)) (k : Fin r) : J (c k) = a k i := by
  have := congrFun (congrFun (coord_unique W T b _ _ h) k) i
  simpa using this

theorem th_inj (hJ : Function.Injective J) : Function.Injective (th W T J b i) := by
  intro c d h
  funext k
  have := th_coord W T J b i (h.trans (th_apply W T J b i d)) k
  simpa using hJ (by simpa using this)

theorem th_mem_N (c : Fin r → O⟦X⟧) : th W T J b i c ∈ W.N T := by
  rw [th_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b k).2

theorem γA_single (g : W.Gam) (x : O⟦X⟧) : W.γA g (Pi.single i x) = Pi.single i (W.γ₀ g x) := by
  funext m
  change W.γ₀ g ((Pi.single i x : LetA O n) m) = _
  by_cases h : m = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem mem_NΔl_iff (hr : ∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a)
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (x : W.DD T) : x ∈ NΔl W T i ↔ ∃ c, th W T J b i c = x := by
  constructor
  · rintro ⟨⟨hx, hΔ⟩, y, hy, hyx⟩
    obtain ⟨a, ha⟩ := exists_coord W T b y hy
    have hxa : x = ∑ k, (Pi.single i (a k i) : LetA O n) • (b k : W.DD T) := by
      rw [← hyx, ha]
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm, letE, mul_single, mul_one]
    have hc : ∀ k, ∃ c, J c = a k i := fun k => (hr _).2 fun δ hδ => by
      have h1 := hΔ δ hδ
      rw [hxa, map_sum] at h1
      simp only [γD_smulA, γA_single, (hb _).2 δ hδ] at h1
      simpa using congrFun (congrFun (coord_unique W T b _ _ h1) k) i
    choose c hc using hc
    exact ⟨c, by rw [hxa, th_apply]; simp only [hc]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨⟨th_mem_N W T J b i c, fun δ hδ => ?_⟩, th W T J b i c, th_mem_N W T J b i c, ?_⟩
    · rw [th_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [γD_smulA, γA_single, (hb _).2 δ hδ, (hr _).1 ⟨_, rfl⟩ δ hδ]
    · change (letE i : LetA O n) • th W T J b i c = _
      rw [smul_th W T J b i (e := 1) (by simp [letE]), one_smul]

theorem γD_mem_NΔl (g : W.Gam) {x : W.DD T} (hx : x ∈ NΔl W T i) : W.γD T g x ∈ NΔl W T i := by
  obtain ⟨⟨hx, hΔ⟩, y, hy, hyx⟩ := hx
  refine ⟨⟨W.N_Γ T g x hx, fun δ hδ => by rw [← W.γD_mul, mul_comm, W.γD_mul, hΔ δ hδ]⟩,
    W.γD T g y, W.N_Γ T g y hy, ?_⟩
  rw [← hyx]
  change (letE i : LetA O n) • W.γD T g y = W.γD T g ((letE i : LetA O n) • y)
  rw [γD_smulA, letE, γA_single, map_one]

theorem γD_th {g : W.Gam} (hJ : QFrame W g J) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (c : Fin r → O⟦X⟧) :
    ∃ c₁ : Fin r → O⟦X⟧, W.γD T g (th W T J b i c) =
      th W T J b i (c + (X - ((PD.p : ℕ) : O⟦X⟧)) • c₁) := by
  obtain ⟨-, hr, -, h0, -⟩ := hJ
  have hc := (mem_NΔl_iff W T J b i hr hb _).2 ⟨c, rfl⟩
  obtain ⟨c', hc'⟩ := (mem_NΔl_iff W T J b i hr hb _).1
    ((NΔl W T i).sub_mem (γD_mem_NΔl W T i g hc) hc)
  obtain ⟨y, hy, hy'⟩ := W.N_π T g _ (th_mem_N W T J b i c)
  obtain ⟨a, ha⟩ := exists_coord W T b y hy
  have h1 : th W T J b i c' = ∑ k, (letπ * a k) • (b k : W.DD T) := by
    rw [hc', hy', ha, Finset.smul_sum]
    simp only [smul_smul]
  have h2 : ∀ k, X - ((PD.p : ℕ) : O⟦X⟧) ∣ c' k := fun k => h0 _ (by
    rw [th_coord W T J b i h1 k]; simp [letπ])
  choose c₁ hc₁ using h2
  refine ⟨c₁, ?_⟩
  have : (X - ((PD.p : ℕ) : O⟦X⟧)) • c₁ = c' := funext fun k => (hc₁ k).symm
  rw [this, map_add, hc']
  abel

theorem mem_qN_iff (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) (j : ℤ) (x : W.DD T) :
    x ∈ qN W T i j ↔ ∃ y ∈ NΔl W T i, ((Qu ^ j : W.EEˣ) : W.EE) • y = x := by
  have hm : ∀ (k : ℕ) (z : W.DD T), mulD W T (qΔ W ^ k) z = (Qu ^ (k : ℤ)) • z := fun k z => by
    change (qΔ W ^ k) • z = ((Qu ^ (k : ℤ) : W.EEˣ) : W.EE) • z
    rw [zpow_natCast, Units.val_pow_eq_pow_val, hQ, ← map_pow, algebraMap_smul]
  simp only [qN, Submodule.mem_comap, Submodule.mem_map, hm]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  change _ ↔ (Qu ^ j) • y = x
  rw [← inv_smul_eq_iff, smul_smul, ← zpow_neg, ← zpow_add]
  rw [show -((-j).toNat : ℤ) + (j.toNat : ℤ) = j by omega]

def cst : O⟦X⟧ →ₐ[O] LetA O n := AlgHom.pi fun _ => J

omit W T b in
theorem cst_apply (c : O⟦X⟧) : (cst J c : LetA O n) i = J c := rfl

def abelian₂ (ζ : LL) : O⟦X⟧ →ₐ[O] LL⟦X⟧ := (W.lev i ζ).comp (cst J)

theorem lev_eq (ζ : LL) {a : LetA O n} {e : O⟦X⟧} (h : a i = J e) : W.lev i ζ a = abelian₂ W J i ζ e := by
  have := W.lev_letter i ζ (a - cst J e) (by rw [Pi.sub_apply, h, cst_apply, sub_self])
  rw [map_sub, sub_eq_zero] at this
  exact this

theorem exists_matrix (ζ : LL) {r' : ℕ} (e : ↥(W.N T) →+ (Fin r' → LL⟦X⟧))
    (he : ∀ a x, e (a • x) = W.lev i ζ a • e x) :
    ∃ M : Matrix (Fin r') (Fin r) LL⟦X⟧,
      (Submodule.span LL⟦X⟧ (Set.range e) = ⊤ → Function.Surjective M.mulVec) ∧
      ∀ c, e ⟨th W T J b i c, th_mem_N W T J b i c⟩ = M.mulVec fun k => abelian₂ W J i ζ (c k) := by
  let M : Matrix (Fin r') (Fin r) LL⟦X⟧ := Matrix.of fun u k => e (b k) u
  have h1 : ∀ a : Fin r → LetA O n, e (∑ k, a k • b k) = M.mulVec fun k => W.lev i ζ (a k) := by
    intro a
    funext u
    simp [M, map_sum, he, Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨M, fun hs => ?_, fun c => ?_⟩
  · have : Submodule.span LL⟦X⟧ (Set.range e) ≤ LinearMap.range M.mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨fun k => W.lev i ζ (b.repr x k), by rw [Matrix.mulVecLin_apply, ← h1, b.sum_repr]⟩
    intro y
    exact this (hs ▸ Submodule.mem_top)
  · have : (⟨th W T J b i c, th_mem_N W T J b i c⟩ : ↥(W.N T)) =
        ∑ k, (Pi.single i (J (c k)) : LetA O n) • b k := by
      apply Subtype.ext
      simp [th_apply]
    rw [this, h1]
    congr 1
    funext k
    exact lev_eq W J i ζ (by simp)

theorem exists_theta {g : W.Gam} (hJ : QFrame W g J) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) (j : ℤ) :
    ∃ θ : (Fin r → O⟦X⟧) ≃ₗ[O] ↥(qN W T i j), ∀ c, (θ c : W.DD T) = (Qu ^ j) • th W T J b i c := by
  let f : (Fin r → O⟦X⟧) →ₗ[O] W.DD T :=
    (Algebra.lsmul O O (W.DD T) ((Qu ^ j : W.EEˣ) : W.EE)).comp (th W T J b i)
  have hf : ∀ c, f c = (Qu ^ j) • th W T J b i c := fun _ => rfl
  have hm : ∀ c, f c ∈ qN W T i j := fun c =>
    (mem_qN_iff W T i Qu hQ j _).2 ⟨_, (mem_NΔl_iff W T J b i hJ.2.1 hb _).2 ⟨c, rfl⟩, rfl⟩
  refine ⟨LinearEquiv.ofBijective (f.codRestrict _ hm) ⟨fun c d h => ?_, fun x => ?_⟩, fun _ => rfl⟩
  · have h1 : f c = f d := congrArg Subtype.val h
    rw [hf, hf] at h1
    exact th_inj W T J b i hJ.1 (MulAction.injective _ h1)
  · obtain ⟨y, hy, hx⟩ := (mem_qN_iff W T i Qu hQ j _).1 x.2
    obtain ⟨c, rfl⟩ := (mem_NΔl_iff W T J b i hJ.2.1 hb _).1 hy
    exact ⟨c, Subtype.ext hx⟩

theorem smul_unit_comm (a : LetA O n) (u : W.EEˣ) (x : W.DD T) : a • u • x = u • a • x := by
  rw [← algebraMap_smul W.EE a, ← algebraMap_smul W.EE a x, Units.smul_def, Units.smul_def, smul_comm]

theorem qΔ_eq {g : W.Gam} (hJ : QFrame W g J) : qΔ W = cst J X := funext fun _ => hJ.2.2.1.symm

theorem zpow_th {g : W.Gam} (hJ : QFrame W g J)
    (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) {j j' : ℤ} (hj : j ≤ j')
    (d : Fin r → O⟦X⟧) : (Qu ^ j') • th W T J b i d =
      (Qu ^ j) • th W T J b i ((X : O⟦X⟧) ^ (j' - j).toNat • d) := by
  rw [← smul_th W T J b i (a := qΔ W ^ (j' - j).toNat) (by rw [qΔ_eq W J hJ, ← map_pow, cst_apply]),
    ← algebraMap_smul W.EE, map_pow, ← hQ, ← Units.val_pow_eq_pow_val, ← Units.smul_def, smul_smul,
    ← zpow_natCast, ← zpow_add]
  rw [show j + ((j' - j).toNat : ℤ) = j' by omega]

theorem theta_mem {g : W.Gam} (hJ : QFrame W g J) (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) {j j' : ℤ} (hj : j ≤ j')
    (c : Fin r → O⟦X⟧) :
    (Qu ^ j) • th W T J b i c ∈ qN W T i j' ↔ ∀ k, (X : O⟦X⟧) ^ (j' - j).toNat ∣ c k := by
  have h1 := zpow_th W T J b i hJ Qu hQ hj
  rw [mem_qN_iff W T i Qu hQ]
  constructor
  · rintro ⟨y, hy, hx⟩ k
    obtain ⟨d, rfl⟩ := (mem_NΔl_iff W T J b i hJ.2.1 hb _).1 hy
    have h2 := th_inj W T J b i hJ.1 (MulAction.injective _ ((h1 d).symm.trans hx))
    exact ⟨d k, (congrFun h2 k).symm⟩
  · intro h
    choose d hd using h
    refine ⟨_, (mem_NΔl_iff W T J b i hJ.2.1 hb _).2 ⟨d, rfl⟩, (h1 d).trans ?_⟩
    congr 2
    exact funext fun k => (hd k).symm

theorem γD_zpow {g : W.Gam} (hJ : QFrame W g J) (s : (O⟦X⟧)ˣ) (hs : W.γ₀ g (J X) = J X * J s)
    (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) (j : ℤ) (x : W.DD T) :
    W.γD T g ((Qu ^ j) • x) = (Qu ^ j) • (cst J ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) : LetA O n) • W.γD T g x := by
  let φ : O⟦X⟧ →* W.EE := ((algebraMap (LetA O n) W.EE).comp (cst J).toRingHom).toMonoidHom
  let ψ : W.EE →* W.EE := (W.γE g).toRingHom.toMonoidHom
  have h1 : Units.map ψ Qu = Qu * Units.map φ s := by
    apply Units.ext
    change W.γE g Qu = Qu * algebraMap (LetA O n) W.EE (cst J s)
    rw [hQ, W.γE_ext, ← map_mul, qΔ_eq W J hJ]
    congr 1
    exact funext fun _ => hs
  have h2 : Units.map ψ (Qu ^ j) = Qu ^ j * Units.map φ (s ^ j) := by
    rw [map_zpow, map_zpow, h1, mul_zpow]
  have h3 : W.γE g ((Qu ^ j : W.EEˣ) : W.EE) = ((Qu ^ j : W.EEˣ) : W.EE) *
      algebraMap (LetA O n) W.EE (cst J ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧)) := congrArg Units.val h2
  rw [Units.smul_def, W.γD_smul, h3, mul_smul, algebraMap_smul, Units.smul_def]

theorem nab_iff {g : W.Gam} (hJ : QFrame W g J) (s : (O⟦X⟧)ˣ) (hs : W.γ₀ g (J X) = J X * J s)
    (Qu : W.EEˣ) (hQ : (Qu : W.EE) = algebraMap (LetA O n) W.EE (qΔ W)) (j : ℤ)
    {a : LetA O n} {a₀ : O⟦X⟧} (ha : a i = J a₀) {c c' d : Fin r → O⟦X⟧}
    (hd : W.γD T g (th W T J b i c) = th W T J b i d) :
    (a * W.π₀) • (Qu ^ j) • th W T J b i c' =
        W.γD T g ((Qu ^ j) • th W T J b i c) - a • (Qu ^ j) • th W T J b i c ↔
      (a₀ * (X - ((PD.p : ℕ) : O⟦X⟧))) • c' = ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) • d - a₀ • c := by
  have h1 : (a * W.π₀) i = J (a₀ * (X - ((PD.p : ℕ) : O⟦X⟧))) := by
    rw [map_mul, map_sub, hJ.2.2.1, map_natCast, add_sub_cancel_right, Pi.mul_apply, ha]
    rfl
  rw [γD_zpow W T J hJ s hs Qu hQ, smul_unit_comm, smul_unit_comm, hd, smul_th W T J b i h1,
    smul_th W T J b i ha, smul_th W T J b i (cst_apply J i _), ← smul_sub, ← map_sub,
    (MulAction.injective _).eq_iff, (th_inj W T J b i hJ.1).eq_iff]

theorem exists_eta [CharZero LL] {g : W.Gam} (hJ : QFrame W g J) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ η : (LL⟦X⟧)ˣ, abelian₂ W J i ζ X = X * (η : LL⟦X⟧) := by
  obtain ⟨E, hE0, hE1, hE⟩ := W.lev_π i ζ ⟨1, by rwa [pow_one]⟩
  obtain ⟨w, hw⟩ := hJ.2.2.2.2.2.1
  have hp := PD.hp
  obtain ⟨E', hE'⟩ : (X : LL⟦X⟧) ∣ E - 1 := by rw [X_dvd_iff]; simp [hE0]
  have hu1 : IsUnit E' := by
    have h1 := congrArg (coeff 0) hE1
    have h2 := congrArg (coeff 1) hE'
    rw [coeff_derivative, coeff_zero_eq_constantCoeff, hE0] at h1
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff, map_sub, coeff_one, if_neg one_ne_zero] at h2
    rw [isUnit_iff_constantCoeff, ← h2]
    simp only [Nat.cast_zero, zero_add, mul_one] at h1
    simp [h1]
  have hu2 : IsUnit (∑ k ∈ Finset.range PD.p, E ^ k) := by
    rw [isUnit_iff_constantCoeff]
    simp [hE0, hp.ne_zero]
  have hu3 : IsUnit (W.lev i ζ letπ) := by
    rw [eq_sub_of_add_eq' hE, isUnit_iff_constantCoeff]
    simpa [hE0, sub_eq_zero] using hζ.ne_one hp.one_lt
  have hu4 : IsUnit (W.lev i ζ fun _ => (w : O⟦X⟧)) := IsUnit.map _ (Pi.isUnit_iff.2 fun _ => w.isUnit)
  have h3 : (letπ : LetA O n) * (cst J X * fun _ => (w : O⟦X⟧)) = (1 + letπ) ^ PD.p - 1 :=
    funext fun _ => by
      change X * (J X * (w : O⟦X⟧)) = (1 + X) ^ PD.p - 1
      rw [hw, W.q₀_def]
  have h4 := congrArg (W.lev i ζ) h3
  rw [map_mul, map_mul, map_sub, map_pow, map_add, map_one, hE, mul_pow, ← map_pow, hζ.pow_eq_one, map_one,
    one_mul, ← mul_geom_sum, hE'] at h4
  refine ⟨(hu1.mul hu2).unit * ((hu3.mul hu4).unit)⁻¹, ?_⟩
  rw [Units.val_mul, ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec, IsUnit.unit_spec]
  change W.lev i ζ (cst J X) * _ = _
  linear_combination h4

theorem diagQuot [IsDomain O] [CharZero LL] (hinj : Function.Injective (algebraMap O LL))
    {g : W.Gam} (hJ : QFrame W g J) (b : Module.Basis (Fin (Module.finrank LL T.V)) (LetA O n) ↥(W.N T))
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (hρ : ∀ f, W.lev i ζ (W.γA g f) = rescale (1 + (PD.p : LL)) (W.lev i ζ f))
    (u : Fin (Module.finrank LL T.V) → ℤ) (e : ↥(W.N T) →+ (Fin (Module.finrank LL T.V) → LL⟦X⟧))
    (he : ∀ a x, e (a • x) = W.lev i ζ a • e x) (hsp : Submodule.span LL⟦X⟧ (Set.range e) = ⊤)
    (hγ : ∀ (x : ↥(W.N T)) hx k, e ⟨W.γD T g x, hx⟩ k =
      C ((1 + (PD.p : LL)) ^ (-u k)) * rescale (1 + (PD.p : LL)) (e x k))
    (a : LetA O n) (a₀ : (O⟦X⟧)ˣ) (ha : a i = J a₀) (ha₁ : X - ((PD.p : ℕ) : O⟦X⟧) ∣ (a₀ : O⟦X⟧) - 1)
    (w : ℤ) (m : (LL⟦X⟧)ˣ)
    (hm : W.lev i ζ a * m = C ((1 + (PD.p : LL)) ^ (-w)) * rescale (1 + (PD.p : LL)) (m : LL⟦X⟧))
    (j j' : ℤ) (hj : j < j') :
    DiagQuot W T g a i j j' (eigMs LL PD.p (Finset.univ.val.map u) w j j') := by
  obtain ⟨s, hs, hs₁⟩ := hJ.2.2.2.2.1
  obtain ⟨Qu, hQ⟩ : IsUnit (algebraMap (LetA O n) W.EE (qΔ W)) := hJ.2.2.2.2.2.2
  obtain ⟨θ, hθ⟩ := exists_theta W T J b i hJ hb Qu hQ j
  have hP : ∀ c, θ c ∈ (qN W T i j').submoduleOf (qN W T i j) ↔
      ∀ k, (X : O⟦X⟧) ^ (j' - j).toNat ∣ c k := fun c => by
    rw [← theta_mem W T J b i hJ hb Qu hQ hj.le, ← hθ]; rfl
  obtain ⟨eq⟩ := quot_equiv _ _ θ hP
  have hp := PD.hp
  have hχ : (1 + (PD.p : LL)) ≠ 0 := by exact_mod_cast (by omega : 1 + PD.p ≠ 0)
  have hX : X - ((PD.p : ℕ) : O⟦X⟧) ≠ 0 := fun h => by
    have := congrArg (coeff 1) h
    rw [← map_natCast (C : O →+* O⟦X⟧), map_sub, coeff_one_X, coeff_C, if_neg one_ne_zero, sub_zero,
      map_zero] at this
    exact one_ne_zero this
  refine ⟨fun x hx => ?_, Module.Free.of_equiv eq.symm, Module.Finite.equiv eq.symm, ?_, ?_, fun nb hnb => ?_⟩
  · obtain ⟨θ', hθ'⟩ := exists_theta W T J b i hJ hb Qu hQ j'
    obtain ⟨c, hc⟩ := θ'.surjective ⟨x, hx⟩
    have h1 : x = (Qu ^ j') • th W T J b i c := by rw [← hθ', hc]
    rw [h1, zpow_th W T J b i hJ Qu hQ hj.le, theta_mem W T J b i hJ hb Qu hQ le_rfl]
    simp
  · rw [eq.finrank_eq]; simp
  · refine exists_factor ((mulD W T (a * W.π₀)).comp (qN W T i j).subtype)
      ((W.γD T g - mulD W T a).comp (qN W T i j).subtype) ?_ fun x => ?_
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨c, rfl⟩ := θ.surjective x
      have h1 := (nab_iff W T J b i hJ s hs Qu hQ j ha (c := 0) (c' := c) (d := 0) (by simp)).1
        (by rw [← hθ, map_zero, smul_zero, map_zero, smul_zero, sub_zero]; exact hx)
      rw [smul_zero, smul_zero, sub_zero, smul_eq_zero_iff_right (mul_ne_zero a₀.ne_zero hX)] at h1
      rw [h1, map_zero]
    · obtain ⟨c, rfl⟩ := θ.surjective x
      obtain ⟨c₁, hc₁⟩ := γD_th W T J b i hJ hb c
      obtain ⟨y, hy⟩ := dvd_zpow_sub_one _ s hs₁ j
      obtain ⟨z, hz⟩ := ha₁
      refine ⟨θ (((a₀⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) • ((y - z) • c + ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) • c₁)), ?_⟩
      have := (nab_iff W T J b i hJ s hs Qu hQ j ha hc₁
        (c' := ((a₀⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) • ((y - z) • c + ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) • c₁))).2 (by
          funext k
          simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
          have := a₀.mul_inv
          linear_combination (c k) * hz - (c k) * hy +
            (X - ((PD.p : ℕ) : O⟦X⟧)) * ((y - z) * c k + ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) * c₁ k) * this)
      rw [← hθ, ← hθ] at this
      exact this
  · obtain ⟨η, hη⟩ := exists_eta W J i hJ ζ hζ
    obtain ⟨M, hM, hMe⟩ := exists_matrix W T J b i ζ e he
    have hMu : IsUnit M.det :=
      (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_surjective_iff_isUnit.1 (hM hsp))
    let Λu : (O⟦X⟧)ˣ →* (LL⟦X⟧)ˣ := Units.map (abelian₂ W J i ζ).toRingHom.toMonoidHom
    obtain ⟨μ, hμ⟩ := exists_mu _ hχ η m (Λu s) (Λu a₀) j w (by
      have h1 := hρ (cst J X)
      rw [lev_eq W J i ζ (e := X * (s : O⟦X⟧)) (by rw [map_mul, ← hs]; rfl), map_mul] at h1
      change _ = rescale _ (abelian₂ W J i ζ X) at h1
      rw [hη, map_mul, rescale_X] at h1
      apply mul_left_cancel₀ (X_ne_zero (R := LL))
      change X * ((η : LL⟦X⟧) * abelian₂ W J i ζ s) = _
      linear_combination h1) (by rw [← hm, lev_eq W J i ζ ha]; rfl)
    rw [← map_zpow] at hμ
    change abelian₂ W J i ζ ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) * (μ : LL⟦X⟧) = C _ * abelian₂ W J i ζ a₀ * _ at hμ
    have hc : constantCoeff (X * (η : LL⟦X⟧) - ((PD.p : ℕ) : LL⟦X⟧)) = -(PD.p : LL) := by simp
    rw [eigMs_eq, ← hc]
    refine GlobalTheory.TruncDiag.diagWith_trunc _ _ _ θ (abelian₂ W J i ζ) η (X * (η : LL⟦X⟧) - ((PD.p : ℕ) : LL⟦X⟧))
      ((μ : LL⟦X⟧) • M) (1 + (PD.p : LL)) (fun k => (1 + (PD.p : LL)) ^ (j + w - u k)) nb hinj hP hη η.isUnit ?_ ?_ hχ ?_
      (fun k => zpow_ne_zero _ hχ) ?_
    · rw [Matrix.det_smul]
      exact (μ.isUnit.pow _).mul hMu
    · rw [hc, neg_ne_zero]
      exact Nat.cast_ne_zero.2 hp.ne_zero
    · intro k hk h
      have h1 : (1 + PD.p) ^ k = 1 := by exact_mod_cast h
      have := hp.pos
      rw [Nat.pow_eq_one] at h1
      omega
    · intro c c' hcc k
      obtain ⟨d, hd⟩ := γD_th W T J b i hJ hb c
      set d' := c + (X - ((PD.p : ℕ) : O⟦X⟧)) • d
      have h1 := hnb (θ c)
      rw [hcc, hθ, hθ, nab_iff W T J b i hJ s hs Qu hQ j ha hd] at h1
      have h2 : (abelian₂ W J i ζ a₀ * (X * (η : LL⟦X⟧) - ((PD.p : ℕ) : LL⟦X⟧))) • (fun k => abelian₂ W J i ζ (c' k)) =
          abelian₂ W J i ζ ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) • (fun k => abelian₂ W J i ζ (d' k)) -
            abelian₂ W J i ζ a₀ • (fun k => abelian₂ W J i ζ (c k)) := by
        funext k
        have := congrArg (abelian₂ W J i ζ) (congrFun h1 k)
        simpa [hη] using this
      have h3 := congrFun (congrArg M.mulVec h2) k
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul] at h3
      have h4 := hγ ⟨_, th_mem_N W T J b i c⟩ (hd ▸ th_mem_N W T J b i d') k
      simp only [hd] at h4
      rw [hMe, hMe] at h4
      simp only [Matrix.smul_mulVec, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul] at h3 ⊢
      rw [h4] at h3
      apply mul_left_cancel₀ (Λu a₀).ne_zero
      change abelian₂ W J i ζ a₀ * _ = abelian₂ W J i ζ a₀ * _
      rw [sub_eq_add_neg (j + w), zpow_add₀ hχ, map_mul]
      linear_combination (μ : LL⟦X⟧) * h3 + C ((1 + (PD.p : LL)) ^ (-u k)) *
        rescale (1 + (PD.p : LL)) (M.mulVec (fun k => abelian₂ W J i ζ (c k)) k) * hμ

def HasCoords (g : W.Gam) (ζ : LL) (r : ℕ) (U : Multiset ℤ) : Prop :=
  ∃ (u : Fin r → ℤ) (e : ↥(W.N T) →+ (Fin r → LL⟦X⟧)), Finset.univ.val.map u = U ∧
    (∀ a x, e (a • x) = W.lev i ζ a • e x) ∧ Submodule.span LL⟦X⟧ (Set.range e) = ⊤ ∧
    ∀ (x : ↥(W.N T)) hx k, e ⟨W.γD T g x, hx⟩ k =
      C ((1 + (PD.p : LL)) ^ (-u k)) * rescale (1 + (PD.p : LL)) (e x k)

theorem coords_of_lines [CharZero LL] (g : W.Gam) (ζ : LL) (U : Multiset ℤ) (h : LinesAt W T i ζ U)
    (hγ : ∀ (x : ↥(W.N T)) hx (k : ℤ), W.levN T i ζ ⟨W.γD T g x, hx⟩ k =
      (1 + (PD.p : LL)) ^ k • W.levN T i ζ x k) : HasCoords W T i g ζ (Module.finrank LL T.V) U := by
  obtain ⟨u, d, hu, hd, hs⟩ := h
  obtain ⟨e, h1, h2, h3⟩ := GlobalTheory.SenLines.Coords.exists_coords (W.lev i ζ) (W.levN T i ζ) u d hd
    (fun a x => funext fun k => W.levN_smul T i ζ a x k) hs
  exact ⟨u, e, hu, h1, h2, fun x hx k => h3 _ x _
    (by exact_mod_cast (by omega : 1 + PD.p ≠ 0)) (hγ x hx) k⟩

theorem senPair [IsDomain O] [IsLocalRing O] [CharZero LL] (hinj : Function.Injective (algebraMap O LL))
    (hl : ¬ IsUnit ((PD.p : ℕ) : O))
    {g : W.Gam} (hJ : QFrame W g J) (b : Module.Basis (Fin (Module.finrank LL T.V)) (LetA O n) ↥(W.N T))
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (hρ : ∀ f, W.lev i ζ (W.γA g f) = rescale (1 + (PD.p : LL)) (W.lev i ζ f))
    (U : Multiset ℤ) (hC : HasCoords W T i g ζ (Module.finrank LL T.V) U)
    (a : LetA O n) (a₀ : (O⟦X⟧)ˣ) (ha : a i = J a₀) (ha₁ : X - ((PD.p : ℕ) : O⟦X⟧) ∣ (a₀ : O⟦X⟧) - 1)
    (w : ℤ) (m : (LL⟦X⟧)ˣ)
    (hm : W.lev i ζ a * m = C ((1 + (PD.p : LL)) ^ (-w)) * rescale (1 + (PD.p : LL)) (m : LL⟦X⟧)) :
    SenPair W T g a i U w := by
  obtain ⟨u, e, hu, he, hsp, hγ⟩ := hC
  have hD : ∀ j j' : ℤ, j < j' → DiagQuot W T g a i j j' (eigMs LL PD.p U w j j') := fun j j' hj =>
    hu ▸ diagQuot W T J i hinj hJ b hb ζ hζ hρ u e he hsp hγ a a₀ ha ha₁ w m hm j j' hj
  refine ⟨hD, fun k _ _ hk => ?_⟩
  obtain ⟨-, hfree, hfin, -, hex, hall⟩ := hD 0 1 zero_lt_one
  refine ⟨hex, fun nb hnb => ?_⟩
  obtain ⟨hs, hd⟩ := hall nb hnb
  refine ⟨hs, ?_⟩
  have hu1 : IsUnit (1 + ((PD.p : ℕ) : O)) := by
    rw [← sub_neg_eq_add]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (fun h => hl (by simpa using h))
  choose c hc hc' using exists_cc (O := O) (F := LL) PD.p PD.hp.ne_zero hu1
  have hk0 : algebraMap O k (PD.p : O) = 0 := by
    have := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (algebraMap O k) hk)
    rw [← RingHom.mem_ker, this]
    exact hl
  have e1 : eigMs LL PD.p U w 0 1 = (U.map fun x => c (0 - (x - w))).map (algebraMap O LL) := by
    rw [eigMs, show Finset.Ico (0 : ℤ) 1 = {0} from rfl, Multiset.map_map, ← Multiset.bind_singleton]
    refine Multiset.bind_congr fun x _ => ?_
    simp only [Finset.singleton_val, Multiset.map_singleton, Function.comp, hc]
  have e2 : (U.map fun x => ((x - w : ℤ) : k)) = (U.map fun x => c (0 - (x - w))).map (algebraMap O k) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    obtain ⟨d, hd⟩ := hc' (0 - (x - w))
    have := congrArg (algebraMap O k) hd
    rw [map_mul, hk0, zero_mul, map_add, map_intCast] at this
    simp only [Function.comp]
    push_cast at this ⊢
    linear_combination -this
  rw [e2]
  rw [e1] at hd
  exact eigWith_of_diagWith hinj _ _ hd

theorem tie_γ {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (tie : CmpTie W E ιdR p1 tS zS) {g : W.Gam} (hχ : algebraMap O LL (W.χΓ g : O) = 1 + (PD.p : LL))
    {ζ : LL} (hζ : IsPrimitiveRoot ζ PD.p) :
    (∀ i f, W.lev i ζ (W.γA g f) = rescale (1 + (PD.p : LL)) (W.lev i ζ f)) ∧
      ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ i (x : ↥(W.N T)) hx (k : ℤ),
        W.levN T i ζ ⟨W.γD T g x, hx⟩ k = (1 + (PD.p : LL)) ^ k • W.levN T i ζ x k := by
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - ((1 : ℕ) : LL)) := by
    rw [hχ, Nat.cast_one, Nat.cast_one, add_sub_cancel_left, W.v_l]
  refine ⟨fun i f => hχ ▸ tie.lev_Γ g i ζ ζ 1 1 (by rwa [pow_one]) hv (pow_one ζ).symm f,
    fun T hT i x hx k => ?_⟩
  rw [tie.levN_eq, tie.levN_eq, tie.levB_Γ T hT g i ζ ζ 1 1 (by rwa [pow_one]) hv (pow_one ζ).symm x hx k,
    map_smul, hχ]

end Generic

theorem finrank_lattice {G LL O V : Type} [Group G] [Field LL] [CommRing O] [IsDomain O] [Algebra O LL]
    [IsPrincipalIdealRing O]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) : Module.finrank O ↥L.T = Module.finrank LL V := by
  have : L.T.IsLattice LL := ⟨L.fg, L.span⟩
  rw [Module.finrank, Module.finrank, Submodule.IsLattice.rank' LL]

end GlobalTheory.SenLines
end
end
