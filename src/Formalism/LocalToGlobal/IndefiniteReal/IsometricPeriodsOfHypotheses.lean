import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.IndefiniteReal.CutPassage

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem fnorm_gram_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ} (w : Fin n → E)
    (hli : LinearIndependent ℂ w) (c : ℝ) (hc : 0 < c) (y : Fin n → ℂ) :
    fnorm (frameOf ((c : ℂ) • Matrix.gram ℂ w)) y = Real.sqrt c * ‖lin w y‖ := by
  have hpd : ((c : ℂ) • Matrix.gram ℂ w).PosDef :=
    (Matrix.posDef_gram_of_linearIndependent hli).smul (Complex.zero_lt_real.mpr hc)
  have hm := (frameOfSpec n _ hpd).2
  set Y := frameOf ((c : ℂ) • Matrix.gram ℂ w) with hY
  have h0 : star y ⬝ᵥ (metOf Y).mulVec y = star (Y⁻¹.mulVec y) ⬝ᵥ Y⁻¹.mulVec y := by
    rw [metOf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  have hg : star y ⬝ᵥ (metOf Y).mulVec y = (c : ℂ) * ⟪lin w y, lin w y⟫_ℂ := by
    rw [hm, Matrix.smul_mulVec, dotProduct_smul, Matrix.star_dotProduct_gram_mulVec, smul_eq_mul]
    rfl
  have h2 : ((∑ i, ‖Y⁻¹.mulVec y i‖ ^ 2 : ℝ) : ℂ) = star (Y⁻¹.mulVec y) ⬝ᵥ Y⁻¹.mulVec y := by
    push_cast
    simp only [dotProduct, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have h3 : ⟪lin w y, lin w y⟫_ℂ = ((‖lin w y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have h1 : (∑ i, ‖Y⁻¹.mulVec y i‖ ^ 2 : ℝ) = c * ‖lin w y‖ ^ 2 := by
    have h4 : ((∑ i, ‖Y⁻¹.mulVec y i‖ ^ 2 : ℝ) : ℂ) = ((c * ‖lin w y‖ ^ 2 : ℝ) : ℂ) := by
      rw [h2, ← h0, hg, h3]
      push_cast
      ring
    exact_mod_cast h4
  unfold fnorm Formalism.HermitianLatticesTheory.cnorm
  rw [h1, Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _)]

theorem cpt_zero' (σ : K →+* ℂ) (n : ℕ) : cpt σ (0 : Fin n → K) = 0 := by
  funext i
  simp [cpt]

theorem cpt_single (σ : K →+* ℂ) {n : ℕ} (i : Fin n) : cpt σ (Pi.single i (1 : K)) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h
    simp [cpt]
  · simp [cpt, h]

theorem bil_expand {a D : ℕ} (Φ : (Fin a → ℂ) →ₗ[ℂ] (Fin D → ℂ) →ₗ[ℂ] ℂ) (x : Fin a → ℂ) (y : Fin D → ℂ) :
    Φ x y = ∑ i, ∑ k, x i * y k * Φ (Pi.single i (1 : ℂ)) (Pi.single k (1 : ℂ)) := by
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℂ) : Fin a → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hy : y = ∑ k, y k • (Pi.single k (1 : ℂ) : Fin D → ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx, hy]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _

theorem mulVec_rinv {d n : ℕ} (P : Matrix (Fin d) (Fin n) K) (h : Function.Surjective P.mulVec) (y : Fin d → K) :
    P.mulVec ((CxData.rinv P).mulVec y) = y := by
  rw [Matrix.mulVec_mulVec, CxData.rinv_spec P h, Matrix.one_mulVec]

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

structure MIDat (fc : DefSub A → DefFace Bs) where

  V : X.EE →ₗ[ℂ] X.EE

  a : (fc X.zs).Dc.Mem → ℂ

  U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ

  ζC : (fc X.zs).Dc.Mem → Bs.Tup → ℂ

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A)

def MIUnit (d : X.MIDat fc) : Prop :=
  (∀ e ∈ X.EEl true, d.V e ∈ X.EEl true ∧ ‖d.V e‖ = ‖e‖) ∧
    (∀ u x, fnorm ((fc X.zs).Dc.Xc u Bs.v0) ((d.U u).mulVec x) = fnorm ((fc X.zs).Dc.Xc u Bs.v0) x) ∧
    (∀ u t, ∃ n : ℕ, 0 < n ∧ d.ζC u t ^ n = 1) ∧ ∀ u, d.ζC u Bs.μ0 = 1

def AuNZ (d : X.MIDat fc) : Prop := ∀ u, d.a u ≠ 0

def MIid (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH)
    (d : X.MIDat fc) : Prop :=
  ∀ u t (φ : Fin ((fc X.zs).Dc.a u) → K) (F : Fin ((fc X.zs).Df1.nV t) → K),
    d.ζC u t * Bs.v0.embedding ((fc X.zs).Dc.Pt u t φ F) =
      d.a u * ⟪sEE (d.V (X.Θ t (X.jR t (eV t F)))), (fc X.zs).Sp.Pu u ((d.U u).mulVec (cpt Bs.v0.embedding φ))⟫_ℂ

def MIstar (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) : Prop :=
  ∃ d : X.MIDat fc, X.MIUnit d ∧ X.MIid eV sEE d ∧ X.AuNZ d

def EVTie (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) : Prop :=
  (∀ t F, eV t F ∈ cv.v0R X.zs true t) ∧
    ∀ t F (x : Fin ((lv (fc X.zs) true).dQ t) → K),
      cv.hR t (cr.toR X.zs true t x) (eV t F) =
        cv.hR t (cr.toR X.zs true t x) (cr.toR X.zs true t (((fc X.zs).Df1.Pq t).mulVec F))

def SEEIso (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) : Prop :=
  (∀ e ∈ X.EEl true, X.nP true * ‖sEE e‖ ^ 2 = ‖e‖ ^ 2) ∧ (∀ e ∈ X.EEl true, sEE e ∈ (fc X.zs).Sp.Rw) ∧
    Module.finrank ℂ (fc X.zs).Sp.Rw = Module.finrank ℂ (X.EEl true)

def zetaOf (d : X.MIDat fc) (u : (fc X.zs).Dc.Mem) (t : Bs.Tup) : K :=
  open Classical in if h : ∃ k : K, Bs.v0.embedding k = d.ζC u t then h.choose else 1

theorem iC_cpt' (b : Bool) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • (Pi.single k (1 : K) : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [iC, map_sum, map_smul, map_smulₛₗ, lin, Fintype.linearCombination_apply, cpt]

theorem theta_eV (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv true) (hDn : X.DnLev cv true) (hUp : X.UpLev cv true) (hC : X.CoordinatesInGoodPart cr cv true)
    (hE : X.EVTie cr cv eV) (t : Bs.Tup) (F : Fin ((fc X.zs).Df1.nV t) → K) :
    X.Θ t (X.jR t (eV t F)) = X.Θ t (X.jR t (cr.toR X.zs true t (((fc X.zs).Df1.Pq t).mulVec F))) := by
  set q : A.FR t := cr.toR X.zs true t (((fc X.zs).Df1.Pq t).mulVec F) with hq
  have hdV : eV t F - q ∈ cv.v0R X.zs true t := sub_mem (hE.1 t F) (hC t _)
  have hdo : ∀ x, cv.hR t (cr.toR X.zs true t x) (eV t F - q) = 0 := by
    intro x; rw [map_sub, hE.2 t F x, sub_self]
  have hjV : X.jR t (eV t F - q) ∈ X.V0C cv true t := Submodule.subset_span ⟨_, hdV, rfl⟩
  have hΘE : X.Θ t (X.jR t (eV t F - q)) ∈ X.EEl true := hDn t ⟨_, hjV, rfl⟩
  have horth : ∀ e ∈ X.EEl true, ⟪e, X.Θ t (X.jR t (eV t F - q))⟫_ℂ = 0 := by
    intro e he
    rw [← LinearMap.adjoint_inner_left]
    have h1 : LinearMap.adjoint (X.Θ t) e ∈
        Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) true).dQ t) → K => X.jR t (cr.toR X.zs true t x)) := by
      rw [hRL t]
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_range_self _ e, hUp t (Submodule.mem_map_of_mem he)⟩
    have h2 : Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) true).dQ t) → K => X.jR t (cr.toR X.zs true t x)) ≤
        (Submodule.span ℂ {X.jR t (eV t F - q)})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm, hJ, hdo x, map_zero]
    have h3 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 h1)
    rwa [inner_eq_zero_symm] at h3
  have h0 : X.Θ t (X.jR t (eV t F - q)) = 0 := inner_self_eq_zero.1 (horth _ hΘE)
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

section Ident

variable {eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH} {d : X.MIDat fc}




theorem zetaOf_spec (u : (fc X.zs).Dc.Mem) (t : Bs.Tup) (h : ∃ k : K, Bs.v0.embedding k = d.ζC u t) :
    Bs.v0.embedding (X.zetaOf d u t) = d.ζC u t := by
  simp only [zetaOf, dif_pos h]
  exact h.choose_spec

theorem zetaOf_not (u : (fc X.zs).Dc.Mem) (t : Bs.Tup) (h : ¬ ∃ k : K, Bs.v0.embedding k = d.ζC u t) :
    X.zetaOf d u t = 1 := by
  simp only [zetaOf, dif_neg h]

theorem zetaOf_pow (hU : X.MIUnit d) (u : (fc X.zs).Dc.Mem) (t : Bs.Tup) :
    ∃ n : ℕ, 0 < n ∧ X.zetaOf d u t ^ n = 1 := by
  obtain ⟨n, hn, hpow⟩ := hU.2.2.1 u t
  by_cases h : ∃ k : K, Bs.v0.embedding k = d.ζC u t
  · refine ⟨n, hn, Bs.v0.embedding.injective ?_⟩
    rw [map_pow, X.zetaOf_spec u t h, hpow, map_one]
  · exact ⟨1, one_pos, by rw [X.zetaOf_not u t h, one_pow]⟩

private theorem vw_pow_lemma {k : K} {n : ℕ} (hn : 0 < n) (hk : k ^ n = 1) (w : HeightOneSpectrum (𝓞 K)) :
    vw w k = 0 := by
  have h1 : (n : ℤ) * vw w k = 0 := by
    unfold vw
    rw [← FractionalIdeal.count_pow]
    first
    | rw [FractionalIdeal.spanSingleton_pow]
    | rw [← FractionalIdeal.spanSingleton_pow]
    rw [hk, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h (by exact_mod_cast hn.ne')
  · exact h

theorem zetaOK_of (hU : X.MIUnit d) : X.ZetaOK (X.zetaOf d) := by
  refine ⟨fun u => ?_, fun u t => ?_, fun u w => ?_⟩
  · have h : ∃ k : K, Bs.v0.embedding k = d.ζC u Bs.μ0 := ⟨1, by rw [map_one, hU.2.2.2 u]⟩
    apply Bs.v0.embedding.injective
    rw [X.zetaOf_spec u Bs.μ0 h, hU.2.2.2 u, map_one]
  · obtain ⟨n, hn, h⟩ := X.zetaOf_pow hU u t
    intro h0
    rw [h0, zero_pow hn.ne'] at h
    exact zero_ne_one h
  · obtain ⟨n, hn, h⟩ := X.zetaOf_pow hU u (X.μ w)
    exact vw_pow_lemma hn h w



end Ident



end CxData

end Formalism.IndefR.Cx
