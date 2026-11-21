import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.NumericalIdentityScalar
import Formalism.LocalToGlobal.PairingIndexBounds.RowActionCoefficients.AdmissibleInterpolation.HighestVectorFullHolds

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace PairingSeriesCoefficients

theorem ev_eq {σ τ K : Type} [Field K] (P : MvPolynomial σ (MvPolynomial τ K)) (d0 : σ → K) :
    eval₂Hom (RingHom.id _) (fun z => C (d0 z)) P = ∑ n ∈ P.support, (∏ i ∈ n.support, d0 i ^ n i) • coeff n P := by
  rw [coe_eval₂Hom, eval₂_eq]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [RingHom.id_apply, smul_eq_C_mul, mul_comm, map_prod]
  simp only [map_pow]

theorem coeff_of_eval {σ τ K : Type} [Field K] [Infinite K] (P : MvPolynomial σ (MvPolynomial τ K))
    (l : MvPolynomial τ K →ₗ[K] K) (R : MvPolynomial σ K)
    (h : ∀ d0 : σ → K, eval d0 R = l (eval₂Hom (RingHom.id _) (fun z => C (d0 z)) P)) (n : σ →₀ ℕ) :
    coeff n R = l (coeff n P) := by
  classical
  have hR : R = ∑ n ∈ P.support, monomial n (l (coeff n P)) := by
    refine MvPolynomial.funext fun d0 => ?_
    rw [h d0, ev_eq, map_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, eval_monomial, smul_eq_mul, mul_comm]
    rfl
  rw [hR, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' P.support n]
  split_ifs with hn
  · rfl
  · rw [notMem_support_iff.1 hn, map_zero]

end PairingSeriesCoefficients

theorem pairing_series_linear_form_holds : PairingSeriesLinearForm := by
  intro p _ X Kc _ _ _ j P f l R h
  have hc := PairingSeriesCoefficients.coeff_of_eval P l R h
  unfold pairD
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hc]
  classical
  rw [Finset.sum_subset (Finset.subset_union_left (s₁ := P.support) (s₂ := R.support)),
    Finset.sum_subset (Finset.subset_union_right (s₁ := P.support) (s₂ := R.support))]
  · intro n _ hn
    rw [← hc, notMem_support_iff.1 hn, mul_zero]
  · intro n _ hn
    rw [notMem_support_iff.1 hn, map_zero, mul_zero]

namespace PairingSeriesCoefficients

section GlobalTheory

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ) (Lk : X.ZA j → X.ZA j → Kc)
  (hne : ∀ x y, Lk x y ≠ 0 → (⟨y.1, y.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) = ⟨x.1, x.2.1⟩)

include hne

theorem isWeightedHomogeneous_linP (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : X.ZA j) :
    IsWeightedHomogeneous (wB X j v s)
      (linP (fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) x) (wB X j v s x) := by
  unfold linP
  refine IsWeightedHomogeneous.sum _ _ _ fun y _ => ?_
  beta_reduce
  by_cases h : Lk x y = 0
  · rw [h, map_zero, map_zero, zero_mul]
    exact isWeightedHomogeneous_zero _ _ _
  · have h2 : wB X j v s x = wB X j v s y := by
      unfold wB
      rw [hne x y h]
    rw [h2]
    exact (isWeightedHomogeneous_X _ _ y).C_mul _

theorem mono_wh (v : X.Pl) (s : Fin (X.G.P.n' v)) (m : X.ZA j →₀ ℕ) :
    IsWeightedHomogeneous (wB X j v s)
      (aeval (linP fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y))
        (monomial m (1 : XspC (X.Pj (j + 1)) Kc))) (Finsupp.weight (wB X j v s) m) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.weight_apply]
  exact IsWeightedHomogeneous.prod _ _ _ fun x _ => (isWeightedHomogeneous_linP X Kc j Lk hne v s x).pow _

theorem hGd (m n : X.ZA j →₀ ℕ)
    (h : coeff n (aeval (linP fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y))
        (monomial m (1 : XspC (X.Pj (j + 1)) Kc))) ≠ 0) : GoodDeg X j n ↔ GoodDeg X j m := by
  have key : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), ∑ a, ∑ b, n ⟨v, (s, a, b)⟩ = ∑ a, ∑ b, m ⟨v, (s, a, b)⟩ := by
    intro v s
    rw [← wt_eq, ← wt_eq]
    by_contra hne'
    exact h ((mono_wh X Kc j Lk hne v s m).coeff_eq_zero n hne')
  unfold GoodDeg
  simp only [key]

theorem pairD_linSub (Q : DA X Kc j) (f : MvPowerSeries (X.ZA j) Kc) :
    pairD X Kc j Q (linSub Lk f) =
      pairD X Kc j (aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) Q) f := by
  classical
  exact pr_sub Lk (GoodDeg X j) (hGd X Kc j Lk hne) Q f

omit hne in

theorem evD_linT (d0 : X.ZA j → Kc) (Q : DA X Kc j) :
    evD X Kc j d0 (aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) Q) =
      evD X Kc j (fun y => ∑ z, Lk z y * d0 z) Q := by
  have h : (evD X Kc j d0).comp
      (aeval (linT fun x y => algebraMap Kc (XspC (X.Pj (j + 1)) Kc) (Lk x y)) :
        DA X Kc j →ₐ[XspC (X.Pj (j + 1)) Kc] DA X Kc j).toRingHom = evD X Kc j (fun y => ∑ z, Lk z y * d0 z) := by
    refine ringHom_ext (fun r => ?_) fun y => ?_
    · simp [evD]
    · simp only [evD, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, linT, map_sum, map_mul,
        coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.id_apply, algebraMap_eq]
  exact RingHom.congr_fun h Q

end GlobalTheory

end PairingSeriesCoefficients

theorem frame_change_pairing_holds : XB := by
  intro p _ X Kc _ _ _ _ j La La' φ P f l R h
  rw [PairingSeriesCoefficients.pairD_linSub X Kc j (bc Kc φ) (fun x y hxy => by
    by_contra hne
    exact hxy (bc_ne Kc φ x y fun h' => hne h'.symm)) P f]
  refine pairing_series_linear_form_holds p X Kc j _ f l R fun d0 => ?_
  rw [h d0, PairingSeriesCoefficients.evD_linT]

theorem transposed_frame_image_blockwise_holds : TransposedFrameImageBlockwise := by
  intro p _ X Kc _ _ _ j La La' φ d0 b
  obtain ⟨v, s⟩ := b
  refine Matrix.ext fun a b' => ?_
  show ∑ z, bc Kc φ z ⟨v, (s, a, b')⟩ * d0 z = _
  rw [sum_block X j (fun z => bc Kc φ z ⟨v, (s, a, b')⟩ * d0 z) v s (fun z hz => by
    rw [bc_ne Kc φ z _ hz, zero_mul])]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dM, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b'' _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [bc_same]
  ring

namespace PairingSeriesCoefficients

section Ev

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem evD_xd (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) (d0 : X.ZA j → Kc) (b' : Fin (NJ X (j + 1))) (i : ℕ) :
    evD X Kc j d0 (xd X Kc j b.1 b.2 x b' i) =
      C (mulC (dM X Kc j b d0).transpose (fun a i => algebraMap X.G.Kf Kc (x a i)) b' i) := by
  simp only [xd, mulC, map_sum, map_mul, Matrix.transpose_apply, dMat, dM, evD, coe_eval₂Hom, eval₂_X, MvPolynomial.algebraMap_apply,
    eval₂_C, RingHom.id_apply]

theorem evD_yMat (b : BX X) (d0 : X.ZA j → Kc) :
    (yMat X Kc j b.1 b.2).map (evD X Kc j d0) =
      (yV Kc (NJ X (j + 1))).map ((rename (emX X (j + 1) b) :
        MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) Kc →ₐ[Kc] XspC (X.Pj (j + 1)) Kc) :
        MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) Kc →+* XspC (X.Pj (j + 1)) Kc) := by
  refine Matrix.ext fun b' t => ?_
  simp only [Matrix.map_apply, yMat, yV, evD, coe_eval₂Hom, eval₂_C, RingHom.id_apply, RingHom.coe_coe, rename_X]
  rfl

end Ev

end PairingSeriesCoefficients

theorem frame_change_compatibility_holds : XC := by
  intro p _ X Kc _ _ j b x d0
  unfold tgtD tgtN
  split_ifs with ho
  · rw [map_hvO, PairingSeriesCoefficients.evD_yMat, ← RingHom.coe_coe (rename (emX X (j + 1) b)), map_hvO]
    congr 1
    funext b' i
    rw [PairingSeriesCoefficients.evD_xd, RingHom.coe_coe, rename_C]
  · rw [map_hvE, PairingSeriesCoefficients.evD_yMat, ← RingHom.coe_coe (rename (emX X (j + 1) b)), map_hvE]
    congr 1
    funext b' i
    rw [PairingSeriesCoefficients.evD_xd, RingHom.coe_coe, rename_C]

namespace PairingSeriesCoefficients

section Deg

theorem det_wh {σ R : Type} [CommRing R] (w : σ → ℕ) {m : ℕ} (M : Matrix (Fin m) (Fin m) (MvPolynomial σ R)) (d : ℕ)
    (h : ∀ i i', IsWeightedHomogeneous w (M i i') d) : IsWeightedHomogeneous w M.det (m * d) := by
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun τ _ => ?_
  have h1 : IsWeightedHomogeneous w (∏ i, M (τ i) i) (m * d) := by
    have := IsWeightedHomogeneous.prod (w := w) Finset.univ (fun i => M (τ i) i) (fun _ => d) fun i _ => h (τ i) i
    rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h2 | h2
  · rw [h2, one_smul]
    exact h1
  · rw [h2, Units.neg_smul, one_smul]
    exact (mem_weightedHomogeneousSubmodule R w _ _).1
      (neg_mem ((mem_weightedHomogeneousSubmodule R w _ _).2 h1))

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ)

theorem colFac_wh (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (b : BX X) (c : ℕ) :
    IsWeightedHomogeneous (wB X j v s) (X.colFac j I b.1 b.2 c)
      (X.colHt b.1 (j + 1) b.2 c * if b = ⟨v, s⟩ then 1 else 0) := by
  unfold Sys.colFac
  refine det_wh _ _ _ fun i i' => ?_
  rw [Matrix.of_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun a _ => ?_
  exact (isWeightedHomogeneous_X _ (wB X j v s) (⟨b.1, (b.2, a, I b.1 b.2 c i'.val)⟩ : X.ZA j)).C_mul _

theorem PI_wh (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    IsWeightedHomogeneous (wB X j v s) (X.PI j I i0)
      (∑ c ∈ Finset.range (X.nuv v (j + 1) s 1).toNat, X.colHt v (j + 1) s c) := by
  classical
  have h1 : X.PI j I i0 = ∏ b : BX X, ∏ c ∈ Finset.range (X.nuv b.1 (j + 1) b.2 1).toNat,
      (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) * X.colFac j I b.1 b.2 c := by
    rw [Fintype.prod_sigma]
    rfl
  have h2 := IsWeightedHomogeneous.prod (w := wB X j v s) (Finset.univ : Finset (BX X))
    (fun b => ∏ c ∈ Finset.range (X.nuv b.1 (j + 1) b.2 1).toNat,
      (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) * X.colFac j I b.1 b.2 c)
    (fun b => ∑ c ∈ Finset.range (X.nuv b.1 (j + 1) b.2 1).toNat,
      (0 + X.colHt b.1 (j + 1) b.2 c * if b = ⟨v, s⟩ then 1 else 0))
    (fun b _ => IsWeightedHomogeneous.prod _ _ _ fun c _ => by
      refine IsWeightedHomogeneous.mul ?_ (colFac_wh X j I v s b c)
      have h3 : (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 b.1 b.2 c) =
          C ((p : MvPolynomial (X.FrI j) ℤ) ^ (X.colExp j I i0 b.1 b.2 c)) := by
        rw [map_pow, map_natCast]
      rw [h3]
      exact isWeightedHomogeneous_C _ _)
  rw [h1]
  convert h2 using 1
  rw [Finset.sum_eq_single (⟨v, s⟩ : BX X)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem PI_good (I : X.ColCh j) (i0 : X.Pl → ℕ) (n : X.ZA j →₀ ℕ) (hn : coeff n (X.PI j I i0) ≠ 0) : GoodDeg X j n := by
  intro v s
  rw [← wt_eq, PI_wh X j I i0 v s hn, Finset.sum_range]
  exact sum_colHt X v j s

end Deg

end PairingSeriesCoefficients

theorem frame_change_group_action_holds : XG := by
  intro p _ X Kc _ _ j I i0 f x
  classical
  rw [Finset.sum_subset (support_map_subset _ _) (fun n _ hn => by rw [notMem_support_iff.1 hn, mul_zero])]
  unfold applyD
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [smul_eval, eval_map, coeff_map, coe_eval₂Hom]
  congr 1
  unfold derAt
  rw [if_pos (PairingSeriesCoefficients.PI_good X j I i0 n (mem_support_iff.1 hn))]

theorem frame_change_injective_holds : XInj := by
  intro p _ X j
  constructor
  · rintro ⟨⟨v, s⟩, a⟩ ⟨⟨v', s'⟩, a'⟩ h
    have h1 := congrArg (idxJ X j) h
    simp only [emX, idxJ_idxI] at h1
    cases h1
    rfl
  · rintro ⟨⟨v, s⟩, a, t⟩ ⟨⟨v', s'⟩, a', t'⟩ h
    simp only [xmX] at h
    cases h
    rfl

end Formalism.L2.PairingIndexBounds.Ent
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.L2.PairingIndexBounds.Ent

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.G.Model.TS

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

namespace XAAux

section Rule

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem NJ_pos : 0 < NJ X j := by
  unfold NJ NN
  omega

theorem hvE_congr {A : Type*} [CommRing A] {n : ℕ} (x : Fin n → ℕ → A) (y : Matrix (Fin n) (Fin n) A) (c : ℕ) (h h' : Fin c → ℕ)
    (hh : ∀ k, h k ≤ n) (hh' : ∀ k, h' k ≤ n) (e : h = h') : hvE x y c h hh = hvE x y c h' hh' := by
  subst e
  rfl

theorem rename_yV (b : BX X) :
    (yV X.G.Kf (NJ X j)).map ((rename (emX X j b) :
      MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf →ₐ[X.G.Kf] (X.Pj j).Xsp) :
      MvPolynomial (Fin (NJ X j) × Fin (NJ X j)) X.G.Kf →+* (X.Pj j).Xsp) = yL X j b.1 b.2 := by
  refine Matrix.ext fun a t => ?_
  simp only [Matrix.map_apply, yV, RingHom.coe_coe, rename_X]
  rfl

theorem rename_hvO (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) :
    rename (emX X j b) (hvO (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) c h) = hvOdd X j b.1 b.2 x c h := by
  rw [← RingHom.coe_coe (rename (emX X j b)), map_hvO, rename_yV]
  unfold hvO hvOdd
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 2
  funext a i
  rw [RingHom.coe_coe, rename_C]

theorem subD_rename_hvE (b : BX X) (ho : ¬ IsOddPos b.2) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ)
    (hh : ∀ k, h k ≤ NJ X j) :
    subD X Kc j (rename (emX X j b) (hvE (fun a i => C (x a i)) (yV X.G.Kf (NJ X j)) c h hh)) =
      hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x a i)) (dyMat X Kc j b.1 b.2) c h hh := by
  rw [← RingHom.coe_coe (rename (emX X j b)), map_hvE, rename_yV, ← RingHom.coe_coe (subD X Kc j), map_hvE]
  congr 1
  · funext a i
    rw [RingHom.coe_coe, RingHom.coe_coe, rename_C]
    exact (subD X Kc j).commutes (x a i)
  · have := subD_yL X Kc j b.1 b.2
    unfold ySub at this
    rw [if_neg ho] at this
    exact this

theorem hvE_dy (b : BX X) (x : Fin (NJ X j) → ℕ → X.G.Kf) (c : ℕ) (h : Fin c → ℕ) (hh : ∀ k, h k ≤ NJ X j)
    (hh' : ∀ k, h k ≤ NJ X (j + 1)) :
    hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x a i)) (dyMat X Kc j b.1 b.2) c h hh =
      hvE (xd X Kc j b.1 b.2 x) (yMat X Kc j b.1 b.2) c h hh' := by
  unfold hvE
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  refine Matrix.ext fun i t => ?_
  rw [Matrix.of_apply, Matrix.of_apply]
  exact pair_dy X Kc j b.1 b.2 x i.val (Fin.castLE (hh k) t)

end Rule

end XAAux

theorem xA_of (hS : XShape) : XA := by
  intro p _ X Kc _ _ j x
  have key := polDel_hv X Kc j (fun v s => x ⟨v, s⟩) (fun v s => cX X j ⟨v, s⟩)
    (fun v s k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val)
    (fun v s => rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩)))
    (fun v s _ k => colH_le _ _) (fun v s _ => cMu_toNat X v j s)
    (fun v s _ => by
      rw [← sum_colHt X v j s]
      congr 1
      exact Finset.sum_congr rfl fun k _ => (hS p X j ⟨v, s⟩).2.2.2.2.1 k.val)
  rw [Fintype.prod_sigma, Fintype.prod_sigma]
  have h1 : (∏ v, ∏ s, rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩))) =
      ∏ v, ∏ s, if IsOddPos s then hvOdd X j v s (x ⟨v, s⟩) (cX X j ⟨v, s⟩) (fun k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val)
        else rename (emX X j ⟨v, s⟩) (srcN X j ⟨v, s⟩ (x ⟨v, s⟩)) := by
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    split_ifs with ho
    · unfold srcN
      rw [if_pos ho]
      exact XAAux.rename_hvO X j ⟨v, s⟩ _ _ _
    · rfl
  rw [h1, key]
  refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
  obtain ⟨-, -, hanti, hle, hc1, hc2, he1, he2, -, -⟩ := hS p X j ⟨v, s⟩
  unfold tgtD
  split_ifs with ho
  · unfold hvOdd' hvO
    refine Finset.prod_congr rfl fun k _ => ?_
    beta_reduce
    rw [hc1, hc2]
  · have hf := highest_vector_full_holds (DA X Kc j) (NJ X j) (muX X j (NJ X j) ⟨v, s⟩) (hanti _) (cX X j ⟨v, s⟩) (eX X j ⟨v, s⟩)
      (hle _) he1 he2 (XAAux.NJ_pos X j) (fun a i => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i)) (dyMat X Kc j v s)
    have hnu : nuS X j ⟨v, s⟩ = fun t => muX X j (NJ X j) ⟨v, s⟩ t - eX X j ⟨v, s⟩ := if_neg ho
    have hdet : (Matrix.of fun a i : Fin (NJ X j) => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i.val)).det =
        algebraMap X.G.Kf (DA X Kc j) (Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det := by
      rw [RingHom.map_det]
      rfl
    have h2 : hvE (xd X Kc j v s (x ⟨v, s⟩)) (yMat X Kc j v s) (cX X j ⟨v, s⟩)
        (fun k => colH (muX X j (NJ X (j + 1)) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val) =
        hvE (fun a i => algebraMap X.G.Kf (DA X Kc j) (x ⟨v, s⟩ a i)) (dyMat X Kc j v s) (cX X j ⟨v, s⟩)
          (fun k => colH (muX X j (NJ X j) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val) := by
      rw [XAAux.hvE_dy X Kc j ⟨v, s⟩ _ _ _ _ (fun k => (colH_le _ k.val).trans (NN_le X j))]
      exact XAAux.hvE_congr _ _ _ _ _ _ _ (funext fun k => by rw [hc1, hc2])
    show _ = hvE (xd X Kc j v s (x ⟨v, s⟩)) (yMat X Kc j v s) (cX X j ⟨v, s⟩)
        (fun k => colH (muX X j (NJ X (j + 1)) ⟨v, s⟩) k.val) (fun k => colH_le _ k.val)
    rw [h2, hf, hdet]
    unfold srcN
    rw [if_neg ho, map_mul, map_mul, rename_C, XAAux.subD_rename_hvE X Kc j ⟨v, s⟩ ho,
      show subD X Kc j (C ((Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det ^ eX X j ⟨v, s⟩)) =
        algebraMap X.G.Kf (DA X Kc j) ((Matrix.of fun a i : Fin (NJ X j) => x ⟨v, s⟩ a i.val).det ^ eX X j ⟨v, s⟩) from
        (subD X Kc j).commutes _, map_pow, mul_pow,
      XAAux.hvE_congr _ _ _ (fun k => colH (nuS X j ⟨v, s⟩) k.val)
        (fun k => colH (fun t => muX X j (NJ X j) ⟨v, s⟩ t - eX X j ⟨v, s⟩) k.val) _ (fun k => colH_le _ k.val) (by rw [hnu])]
    show _ * _ * (dyMat X Kc j v s).det ^ eX X j ⟨v, s⟩ = _
    ring

namespace XAAux

section Span

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (j : ℕ)

theorem pairD_mem [Infinite Kc] (W : Submodule Kc (XspC (X.Pj (j + 1)) Kc)) (P : DA X Kc j)
    (h : ∀ d0 : X.ZA j → Kc, evD X Kc j d0 P ∈ W) (f : MvPowerSeries (X.ZA j) Kc) : pairD X Kc j P f ∈ W := by
  by_contra hn
  obtain ⟨l, hl, hW⟩ := Submodule.exists_le_ker_of_notMem hn
  refine hl ?_
  rw [pairing_series_linear_form_holds p X Kc j P f l 0 fun d0 => by rw [map_zero, LinearMap.mem_ker.1 (hW (h d0))]]
  simp

theorem map_bidet {K K' : Type} [CommRing K] [CommRing K'] (φ : K →+* K') {r n c : ℕ} (sz : Fin c → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : map φ (bideterminant K sz hsz I) = bideterminant K' sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem tgtN_mem [CharZero Kc] (hS : XShape) (b : BX X) (z : Fin (NJ X (j + 1)) → ℕ → Kc) :
    tgtN X Kc j b z ∈ dualWeyl Kc (NJ X (j + 1)) (NJ X (j + 1)) (nuT X j b) := by
  obtain ⟨-, -, hanti, hle, -⟩ := hS p X j b
  unfold tgtN nuT
  split_ifs with ho
  · exact highest_vector_mem_odd Kc _ _ (hanti _) _ (hle _) z
  · exact highest_vector_mem_even Kc _ _ (hanti _) _ (hle _) z

end Span

end XAAux

theorem xSpanN_of (hS : XShape) : XSpanN := by
  intro p _ X Kc _ _ _ j x f
  classical
  rw [delF_apply, xA_of hS p X Kc j x]
  refine XAAux.pairD_mem X Kc j _ _ (fun d0 => ?_) f
  rw [map_prod]
  simp only [frame_change_compatibility_holds p X Kc j]
  refine prod_span (R := Kc) (fun b : BX X => {y : XspC (X.Pj (j + 1)) Kc |
      ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ NJ X (j + 1)) (I : ∀ k, Fin (sz k) → Fin (NJ X (j + 1))),
        shapeDeg sz = nuT X j b ∧ y = rename (emX X (j + 1) b) (bideterminant Kc sz hsz I)}) _ (fun g hg => ?_) _ (fun b => ?_)
  · choose K sz hsz I hsh hgb using hg
    refine Submodule.subset_span ⟨fun b => bideterminant X.G.Kf (sz b) (hsz b) (I b), fun b => ?_, ?_⟩
    · rw [← hsh b]
      exact bidetMem X.G.Kf _ _ _ _ _ _
    · rw [map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [hgb b, map_rename, XAAux.map_bidet]
  · have h1 := XAAux.tgtN_mem X Kc j hS b
      (mulC (dM X Kc j b d0).transpose fun a i => algebraMap X.G.Kf Kc (x b a i))
    rw [standardMonomialSpanDomain Kc] at h1
    have h2 := Submodule.mem_map_of_mem (f := (rename (emX X (j + 1) b) :
      MvPolynomial (Fin (NJ X (j + 1)) × Fin (NJ X (j + 1))) Kc →ₐ[Kc] XspC (X.Pj (j + 1)) Kc).toLinearMap) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨q, ⟨K, sz, hsz, I, hsh, rfl⟩, rfl⟩
    exact ⟨K, sz, hsz, I, hsh, rfl⟩

end Formalism.L2.PairingIndexBounds.Ent
end
end
