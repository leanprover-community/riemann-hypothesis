import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds

section
noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

lemma neg_vAdd_le (w : HeightOneSpectrum (𝓞 K)) (x c : K) (hc : c ≠ 0)
    (hci : w.valuation K c ≤ 1) (d : ℕ) (h : w.valuation K x * (w.valuation K c) ^ d ≤ 1) :
    -vAdd w x ≤ (d : ℤ) * vAdd w c := by
  have hc0 : w.valuation K c ≠ 0 := by simpa using hc
  have hlc : WithZero.log (w.valuation K c) ≤ 0 := by
    rw [← WithZero.log_one]
    exact (WithZero.log_le_log hc0 one_ne_zero).2 hci
  unfold vAdd
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, WithZero.log_zero, neg_zero]
    nlinarith
  · have hx0 : w.valuation K x ≠ 0 := by simpa using hx
    have hp : w.valuation K x * (w.valuation K c) ^ d ≠ 0 := mul_ne_zero hx0 (pow_ne_zero _ hc0)
    have := (WithZero.log_le_log hp one_ne_zero).2 h
    rw [WithZero.log_mul hx0 (pow_ne_zero _ hc0), WithZero.log_pow, WithZero.log_one] at this
    simp only [nsmul_eq_mul] at this
    linarith

lemma val_det_le {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin d) (Fin d) K) (c : K)
    (hM : ∀ i j, w.valuation K (M i j) * w.valuation K c ≤ 1) :
    w.valuation K M.det * (w.valuation K c) ^ d ≤ 1 := by
  have key : w.valuation K (c • M).det ≤ 1 := by
    rw [Matrix.det_apply]
    refine Valuation.map_sum_le _ (fun σ _ => ?_)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul, map_prod]
      refine Finset.prod_le_one' (fun i _ => ?_)
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, mul_comm]
      exact hM _ _
    · rw [hs, Units.neg_smul, one_smul, Valuation.map_neg, map_prod]
      refine Finset.prod_le_one' (fun i _ => ?_)
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, mul_comm]
      exact hM _ _
  rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow] at key
  rwa [mul_comm]

lemma val_eq_one_of_not_mem (w : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (hs : s ∉ w.asIdeal) :
    w.valuation K (algebraMap (𝓞 K) K s) = 1 := by
  refine le_antisymm (w.valuation_le_one s) ?_
  by_contra hlt
  exact hs ((w.valuation_lt_one_iff_mem s).1 (not_le.1 hlt))

lemma val_le_one_of_mem_range (w : HeightOneSpectrum (𝓞 K)) (x : K)
    (hx : x ∈ Set.range (algebraMap (𝓞 K) K)) : w.valuation K x ≤ 1 := by
  obtain ⟨r, rfl⟩ := hx
  exact w.valuation_le_one r

lemma val_star_eq_one (w w' : HeightOneSpectrum (𝓞 K)) (hww : IsConjPlK w w') (s : 𝓞 K)
    (hs : s ∉ w'.asIdeal) : w.valuation K (star (algebraMap (𝓞 K) K s)) = 1 := by
  have h1 := val_eq_one_of_not_mem w' s hs
  have hv : vAdd w' (algebraMap (𝓞 K) K s) = 0 := by
    unfold vAdd; rw [h1, WithZero.log_one, neg_zero]
  rw [hww] at hv
  have hne : star (algebraMap (𝓞 K) K s) ≠ 0 := by
    intro h0
    have : algebraMap (𝓞 K) K s = 0 := by simpa using congrArg star h0
    rw [this, map_zero] at h1
    exact zero_ne_one h1
  have hv0 : w.valuation K (star (algebraMap (𝓞 K) K s)) ≠ 0 := by simpa using hne
  unfold vAdd at hv
  have : WithZero.log (w.valuation K (star (algebraMap (𝓞 K) K s))) = 0 := by linarith
  rw [← WithZero.exp_log hv0, this, WithZero.exp_zero]

lemma h_smul_left {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) (x y : V) :
    h (c • x) y = star (algebraMap (𝓞 K) K c) * h x y := by
  rw [← algebraMap_smul K c x, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

lemma h_smul_right {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 K) (x y : V) :
    h x (c • y) = algebraMap (𝓞 K) K c * h x y := by
  rw [← algebraMap_smul K c y, map_smul, smul_eq_mul]

lemma card_le_of_orth (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (hee : e * e = e) (hH : IsHermE A e h) (U : Submodule K A.V) (hU : U ≤ LinearMap.range e)
    {d : ℕ} (y : Fin d → A.V) (hy : LinearIndependent K y) (hye : ∀ i, y i ∈ LinearMap.range e)
    (hyU : ∀ i, ∀ u ∈ U, h (y i) u = 0) :
    d + Module.finrank K U ≤ dimE A e := by
  classical
  haveI : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  have hidem : ∀ x ∈ LinearMap.range e, e x = x := by
    rintro x ⟨z, rfl⟩
    change (e * e) z = e z
    rw [hee]
  let Θ : A.V →ₗ[K] (Fin d → K) := LinearMap.pi (fun i => (h (y i)).comp e)
  have hsurj : LinearMap.range Θ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let a : Fin d → K := fun i => f (fun j => if i = j then 1 else 0)
    have hfa : ∀ v : Fin d → K, f v = ∑ i, a i * v i := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ v]
      simp only [map_sum, map_smul, smul_eq_mul, a]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_comm]
    let z : A.V := ∑ i, star (a i) • y i
    have hz : ∀ x, h z x = 0 := by
      intro x
      have hze : z ∈ LinearMap.range e :=
        Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hye i))
      have h1 : h z x = h z (e x) := by
        rw [← hH.2.2, hidem z hze]
      have h2 : f (Θ x) = 0 := hle ⟨x, rfl⟩
      rw [hfa] at h2
      rw [h1]
      simp only [z, map_sum, LinearMap.sum_apply, map_smulₛₗ, starRingEnd_apply, star_star,
        LinearMap.smul_apply, smul_eq_mul]
      simpa [Θ] using h2
    have hz0 : z = 0 := hH.2.1 z hz
    have ha : ∀ i, a i = 0 := by
      intro i
      have := (Fintype.linearIndependent_iff.1 hy) (fun i => star (a i)) hz0 i
      simpa using this
    apply hf0
    apply LinearMap.ext
    intro v
    rw [hfa]
    simp [ha]
  have hrn := LinearMap.finrank_range_add_finrank_ker Θ
  rw [hsurj, finrank_top, Module.finrank_fin_fun] at hrn
  have hrn2 := LinearMap.finrank_range_add_finrank_ker e
  have hsup : U ⊔ LinearMap.ker e ≤ LinearMap.ker Θ := by
    refine sup_le (fun u hu => ?_) (fun x hx => ?_)
    · rw [LinearMap.mem_ker]
      funext i
      simp [Θ, hidem u (hU hu), hyU i u hu]
    · rw [LinearMap.mem_ker] at hx ⊢
      funext i
      simp [Θ, hx]
  have hinf : U ⊓ LinearMap.ker e = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hu, hk⟩
    have hk' : e u = 0 := LinearMap.mem_ker.1 hk
    rw [Submodule.mem_bot, ← hidem u (hU hu), hk']
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker e)
  rw [hinf, finrank_bot] at h3
  have h4 := Submodule.finrank_mono hsup
  unfold dimE
  omega

theorem partA (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (hP : IsProj A e n) (hH : IsHermE A e h) (hD : ∀ w, DualInAt A h A.L w)
    (U : Submodule K A.V) (hU : U ≤ LinearMap.range e) (w : HeightOneSpectrum (𝓞 K)) (k : ℤ)
    (hk : IsValG A e h U w k) :
    k ≤ ((dimE A e : ℤ) - (Module.finrank K U : ℤ)) * vAdd w ((n : ℕ) : K) := by
  classical
  obtain ⟨hG, hn, hee, hnL, -⟩ := hP
  obtain ⟨w', hww, d, y, hy, hloc, rfl⟩ := hk
  have hidem : ∀ x ∈ LinearMap.range e, e x = x := by
    rintro x ⟨z, rfl⟩
    change (e * e) z = e z
    rw [hee]
  have hw : w ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))) := Or.inl rfl
  have hw' : w' ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))) := Or.inr rfl
  have hy_props : ∀ i, y i ∈ LinearMap.range e ∧ ∀ u ∈ U, h (y i) u = 0 := by
    intro i
    obtain ⟨s, hs, hL⟩ := (hloc w hw).1 i
    have hs0 : (algebraMap (𝓞 K) K s) ≠ 0 := by
      intro h0
      have h00 : s = 0 := IsFractionRing.injective (𝓞 K) K (by rw [h0, map_zero])
      exact hs (h00 ▸ w.asIdeal.zero_mem)
    obtain ⟨h1, h2, -⟩ := hL
    rw [← algebraMap_smul K s (y i)] at h1 h2
    refine ⟨?_, fun u hu => ?_⟩
    · have := Submodule.smul_mem (LinearMap.range e) (algebraMap (𝓞 K) K s)⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at this
    · have := h2 u hu
      rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at this
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd (by simpa using h0) hs0
      · exact h0
  have hcard := card_le_of_orth A e h hee hH U hU y hy (fun i => (hy_props i).1)
    (fun i => (hy_props i).2)
  have hnK : ((n : ℕ) : K) ≠ 0 := by exact_mod_cast hn.ne'
  have hnval : w.valuation K ((n : ℕ) : K) ≤ 1 := by
    have := w.valuation_le_one (K := K) (n : 𝓞 K)
    simpa using this
  have hent : ∀ i j, w.valuation K (h (y i) (y j)) * w.valuation K ((n : ℕ) : K) ≤ 1 := by
    intro i j
    obtain ⟨a, ha, hLa⟩ := (hloc w' hw').1 i
    obtain ⟨b, hb, hLb⟩ := (hloc w hw).1 j
    set v : A.V := ((n : ℕ) : 𝓞 K) • (b • y j) with hv
    have hvint : ∀ m ∈ A.L, h v m ∈ Set.range (algebraMap (𝓞 K) K) := by
      intro m hm
      have hbe : b • y j ∈ LinearMap.range e := hLb.1
      have h1 : h v m = h (b • y j) (((n : ℕ) : 𝓞 K) • e m) := by
        rw [hv, h_smul_left, h_smul_right, ← hH.2.2, hidem _ hbe]
        simp
      rw [h1]
      exact hLb.2.2 _ ⟨hnL m hm, Submodule.smul_mem _ _ (LinearMap.mem_range_self e m)⟩
    obtain ⟨t, ht, htv⟩ := hD w v hvint
    have htcut : t • v ∈ cutE A e A.L := by
      refine ⟨htv, ?_⟩
      show t • v ∈ LinearMap.range e
      exact Submodule.smul_of_tower_mem _ t (Submodule.smul_of_tower_mem _ _ hLb.1)
    have hint := hLa.2.2 _ htcut
    have heq : h (a • y i) (t • v) = star (algebraMap (𝓞 K) K a) *
        (algebraMap (𝓞 K) K t * (((n : ℕ) : K) * (algebraMap (𝓞 K) K b * h (y i) (y j)))) := by
      rw [hv, h_smul_left, h_smul_right, h_smul_right, h_smul_right]
      simp only [map_natCast]
    have hv1 := val_le_one_of_mem_range w _ hint
    rw [heq, map_mul, map_mul, map_mul, map_mul, val_star_eq_one w w' hww a ha,
      val_eq_one_of_not_mem w t ht, val_eq_one_of_not_mem w b hb] at hv1
    simpa [mul_comm] using hv1
  have hdet := val_det_le w (Matrix.of fun i j => h (y i) (y j)) ((n : ℕ) : K) (by simpa using hent)
  have := neg_vAdd_le w _ _ hnK hnval d hdet
  have hvn : 0 ≤ vAdd w ((n : ℕ) : K) := by
    unfold vAdd
    rw [neg_nonneg, ← WithZero.log_one]
    exact (WithZero.log_le_log (by simpa using hnK) one_ne_zero).2 hnval
  have hd : (d : ℤ) ≤ (dimE A e : ℤ) - (Module.finrank K U : ℤ) := by omega
  calc -vAdd w (Matrix.of fun i j => h (y i) (y j)).det ≤ (d : ℤ) * vAdd w ((n : ℕ) : K) := this
    _ ≤ _ := mul_le_mul_of_nonneg_right hd hvn

theorem partC (A : HLat K) (e : Module.End K A.V) (U : Submodule K A.V) :
    ∀ φ ∈ A.dualL, (∀ u ∈ U, φ u = 0) →
      ∀ m ∈ cutE A e A.L, φ m ∈ Set.range (algebraMap (𝓞 K) K) := by
  intro φ hφ _ m hm
  exact hφ m hm.1

end PI.DvRows
end
end

section
noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv

def PartB : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → IsCMFormE A e h →
    (∀ w, DualInAt A h A.L w) → ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ γ : HeightOneSpectrum (𝓞 K) → ℤ, (∀ w, IsValG A e h U w (γ w)) →
      degL A (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) - degL A (cutE A e A.L) ≤
        ∑ᶠ w, lw K w * (γ w : ℝ)


end PI.DvRows
end
end

section
noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

lemma star_mem_range (c : 𝓞 K) : star (algebraMap (𝓞 K) K c) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have hc : IsIntegral ℤ (algebraMap (𝓞 K) K c) := c.2
  have : IsIntegral ℤ ((starRingEnd K) (algebraMap (𝓞 K) K c)) := hc.map (starRingEnd K).toIntAlgHom
  exact ⟨⟨_, this⟩, rfl⟩

def lamSub (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (U : Submodule K A.V) : Submodule (𝓞 K) A.V where
  carrier := {y | LamStar A e h U y}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨Submodule.add_mem _ hx1 hy1, fun u hu => ?_, fun m hm => ?_⟩
    · rw [map_add, LinearMap.add_apply, hx2 u hu, hy2 u hu, add_zero]
    · rw [map_add, LinearMap.add_apply]
      obtain ⟨a, ha⟩ := hx3 m hm
      obtain ⟨b, hb⟩ := hy3 m hm
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, fun u _ => by simp, fun m _ => ⟨0, by simp⟩⟩
  smul_mem' := by
    rintro c y ⟨hy1, hy2, hy3⟩
    refine ⟨?_, fun u hu => ?_, fun m hm => ?_⟩
    · exact Submodule.smul_of_tower_mem _ c hy1
    · rw [h_smul_left, hy2 u hu, mul_zero]
    · rw [h_smul_left]
      obtain ⟨a, ha⟩ := hy3 m hm
      obtain ⟨s, hs⟩ := star_mem_range c
      exact ⟨s * a, by rw [map_mul, ha, hs]⟩

def DegDual : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → IsCMFormE A e h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
      degL A (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) - degL A (cutE A e A.L) =
        degL A (lamSub A e h U)

def DegDualBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → IsCMFormE A e h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ γ : HeightOneSpectrum (𝓞 K) → ℤ, (∀ w, IsValG A e h U w (γ w)) →
      degL A (lamSub A e h U) ≤ ∑ᶠ w, lw K w * (γ w : ℝ)


end PI.DvRows
end
end

section
noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv

def Hyp (K : Type) [Field K] [NumberField K] [StarRing K] (A : HLat K) (e : Module.End K A.V) (n : ℕ)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  StarIsConj K ∧ IsProj A e n ∧ IsHermE A e h ∧ IsCMFormE A e h

def LamFG : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e → (lamSub A e h U).FG

def GramCS : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ (d : ℕ) (y : Fin d → A.V), LinearIndependent K y →
      (Matrix.of fun i j => h (y i) (y j)).det ≠ 0 ∧
      Real.log |((Algebra.norm ℚ (Matrix.of fun i j => h (y i) (y j)).det : ℚ) : ℝ)| ≤
        2 * ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re

def LocalGamma : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ (d : ℕ) (y : Fin d → A.V), LinearIndependent K y → (∀ i, y i ∈ lamSub A e h U) →
      Submodule.span K (lamSub A e h U : Set A.V) = Submodule.span K (Set.range y) →
      ∀ (w : HeightOneSpectrum (𝓞 K)) (k : ℤ), IsValG A e h U w k →
      ∀ w' : HeightOneSpectrum (𝓞 K), IsConjPlK w w' →
        k = -vAdd w (Matrix.of fun i j => h (y i) (y j)).det -
          Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range y)) (lamSub A e h U) -
          Formalism.HermitianLatticesTheory.lidx w'.asIdeal (Submodule.span (𝓞 K) (Set.range y)) (lamSub A e h U)

def ConjPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    ∃ c : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K), Function.Involutive c ∧
      ∀ w, IsConjPlK w (c w) ∧ Ideal.absNorm (c w).asIdeal = Ideal.absNorm w.asIdeal

def NormFinsum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : K), x ≠ 0 →
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw K w * (vAdd w x : ℝ) =
      Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| / (Module.finrank ℚ K : ℝ)

def ArchIdentity : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ (k d : ℕ) (u : Fin k → A.V) (z : Fin d → A.V) (y : Fin d → A.V),
      LinearIndependent K (Fin.append u z) →
      Submodule.span K (Set.range (Fin.append u z)) = LinearMap.range e →
      Submodule.span K (Set.range u) = U →
      LinearIndependent K y → (∀ i, y i ∈ LinearMap.range e) → (∀ i, ∀ x ∈ U, h (y i) x = 0) →
      ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v (Fin.append u z)).det.re -
        ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v u).det.re +
        ∑ v, Real.log (Formalism.HN.gramPl A.b A.X v y).det.re =
        Real.log |((Algebra.norm ℚ (Matrix.of fun i j => h (y i) (z j)).det : ℚ) : ℝ)|

def LocalPairing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), Hyp K A e n h →
    ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    ∀ (k d : ℕ) (u : Fin k → A.V) (z : Fin d → A.V) (y : Fin d → A.V),
      LinearIndependent K (Fin.append u z) →
      Submodule.span K (Set.range (Fin.append u z)) = LinearMap.range e →
      Submodule.span K (Set.range u) = U →
      (∀ i, Fin.append u z i ∈ cutE A e A.L) →
      LinearIndependent K y → (∀ i, y i ∈ lamSub A e h U) →
      Submodule.span K (lamSub A e h U : Set A.V) = Submodule.span K (Set.range y) →
      ∀ w w' : HeightOneSpectrum (𝓞 K), IsConjPlK w w' →
        vAdd w (Matrix.of fun i j => h (y i) (z j)).det +
          Formalism.HermitianLatticesTheory.lidx w'.asIdeal (Submodule.span (𝓞 K) (Set.range y)) (lamSub A e h U) +
          Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range (Fin.append u z))) (cutE A e A.L) -
          Formalism.HermitianLatticesTheory.lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range u))
            (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) = 0

end PI.DvRows
end
end
