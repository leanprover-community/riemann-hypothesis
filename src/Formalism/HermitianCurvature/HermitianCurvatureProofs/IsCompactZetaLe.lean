import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairLevStarMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairOperatorCommute

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Gen

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem Ts_mem (σ : Site A) (hp : σ.p ∈ 𝒜) (hc : σ.c ∈ 𝒜) (hci : σ.ci ∈ 𝒜) (Y : ℂ) (i j : Fin 2) :
    Ts σ Y i j ∈ 𝒜 := by
  unfold Ts Formalism.YangianSpanCharacter.T.Tm
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact add_mem (algebraMap_mem 𝒜 Y) hp
  · exact neg_mem hc
  · exact hci
  · exact zero_mem 𝒜

theorem bT_mem (σ : Site A) (hp : σ.p ∈ 𝒜) (hc : σ.c ∈ 𝒜) (hci : σ.ci ∈ 𝒜) (w : List (Letter ℂ S)) :
    bT σ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [bT]
    refine (entSub 𝒜).mul_mem (ins_mem _ fun i j => ?_) ih
    show io ((if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) i j) ∈ entSub 𝒜
    apply io_mem
    split_ifs
    · exact Ts_mem σ hp hc hci l.pt i j
    · exact (star_mem (Ts_mem σ hp hc hci l.pt i j) : star _ ∈ 𝒜)

end Gen

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}


end Lev

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]


end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsInner_eq_sum (A C : Wq →L[ℂ] Wp) :
    B.hsInner A C = ∑ m, ⟪C (stdOrthonormalBasis ℂ Wq m), A (stdOrthonormalBasis ℂ Wq m)⟫_ℂ := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply]

end HS

section Adj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pairAt_t_adj_cpt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (Φ Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (hK : ∃ K : Set (Mx P.k P.r), IsCompact K ∧ K ⊆ {g | 0 < GGl P.k P.r z z' g} ∧
      ∀ g ∈ Glev P.k P.r (Fin.last P.r), g ∉ K →
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0)
    (Y : ℂ) (a b : Fin 2)
    (h1 : ∀ m, Integrable (fun x : Mt P.k P.r =>
      ⟪(Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m),
        (X.t Y a b Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m)⟫_ℂ) μ)
    (h2 : ∀ m, Integrable (fun x : Mt P.k P.r =>
      ⟪(X.t (star Y) b a Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m),
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c (Matrix.of x) (stdOrthonormalBasis ℂ Wq m)⟫_ℂ) μ) :
    pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c := by
  have hA := Formalism.FourierDecayAlt.P.actual_adjointness Wp Wq P z z' π π' hP X μ hμ Φ Ψ c hc hK Y a b
  simp only [pairAt, hsInner_eq_sum]
  rw [integral_finsetSum _ (fun m _ => h1 m), integral_finsetSum _ (fun m _ => h2 m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e := congrArg (starRingEnd ℂ) (hA (stdOrthonormalBasis ℂ Wq m))
  rw [← integral_conj, ← integral_conj] at e
  simp only [inner_conj_symm] at e
  exact e

end Adj

end Formalism.FourierDecayAlt.P5.HerA
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Cpt

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem cslice_continuous (c : Fin r → ℂ) : Continuous (fun x : Mt k r => (c, Matrix.of x)) :=
  continuous_const.prodMk continuous_id

theorem int_cpt_gen (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Θ : RadSp k r z z' π π') (c : Fin r → ℂ) (v : Wq) (K : Set (Mx k r)) (hKc : IsCompact K)
    (hKG : K ⊆ {g | 0 < GGl k r z z' g}) (hc : c ∈ OmX r)
    (f : Mt k r → ℂ) (hf : (f = fun x => ⟪(Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ) ∨
      (f = fun x => ⟪(Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ))
    (hΦ0 : ∀ g ∈ Glev k r (Fin.last r), g ∉ K → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) :
    Integrable f μ := by
  obtain ⟨s, hs⟩ : ∃ s : Set (Mt k r), s = (fun x : Mt k r => (c, Matrix.of x)) ⁻¹' DomR k r z z' := ⟨_, rfl⟩
  have hsm : MeasurableSet s := by
    rw [hs, DomR_eq, Set.preimage_inter]
    exact ((P.Qx5.isOpen_OpR k r z z').preimage (cslice_continuous c)).measurableSet.inter
      (((P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage (cslice_continuous c)).measurableSet
  have hA : ∀ Ξ : RadSp k r z z' π π', ContinuousOn (fun x : Mt k r => (Ξ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v) s := by
    intro Ξ
    have h1 := (radSp_continuousOn Ξ).comp ((cslice_continuous c).continuousOn : ContinuousOn _ s) (fun x hx => by rw [hs] at hx; exact hx)
    exact h1.clm_apply continuousOn_const
  have hcont : ContinuousOn f s := by
    rcases hf with rfl | rfl
    · exact (hA Φ).inner (hA Θ)
    · exact (hA Θ).inner (hA Φ)
  have hzero : ∀ x, (c, Matrix.of x) ∉ DomR k r z z' ∨ Matrix.of x ∉ K → f x = 0 := by
    intro x hx
    have hΦx : (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) = 0 := by
      rcases hx with hx | hx
      · exact radSp_zero_off Φ (x := (c, Matrix.of x)) hx
      · by_cases hg : Matrix.of x ∈ Glev k r (Fin.last r)
        · exact hΦ0 _ hg hx
        · exact radSp_zero_off Φ (x := (c, Matrix.of x)) (fun h => hg h.2.1)
    rcases hf with h | h
    · subst h
      show ⟪(Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v, (Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ = 0
      rw [hΦx, _root_.zero_apply, inner_zero_left]
    · subst h
      show ⟪(Θ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v, (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ = 0
      rw [hΦx, _root_.zero_apply, inner_zero_right]
  obtain ⟨C, hC⟩ : ∃ C : Set (Mt k r), C = (fun g : Mx k r => (Matrix.of.symm g : Mt k r)) '' (K ∩ Glev k r (Fin.last r)) :=
    ⟨_, rfl⟩
  have hCmem : ∀ x, x ∈ C ↔ Matrix.of x ∈ K ∧ Matrix.of x ∈ Glev k r (Fin.last r) := by
    intro x
    rw [hC]
    constructor
    · rintro ⟨g, hg, rfl⟩; simpa using hg
    · intro hx; exact ⟨Matrix.of x, hx, rfl⟩
  have hCc : IsCompact C := by
    rw [hC]
    exact (hKc.inter_right (P.Qx5.Glev_closed _)).image continuous_id
  have hCs : C ⊆ s := by
    intro x hx
    rw [hCmem] at hx
    rw [hs]
    exact ⟨hc, hx.2, hKG hx.1⟩
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (hcont.mono hCs)
  have hmeas : Measurable f := measurable_of_continuousOn_zero hsm hcont (fun x hx => hzero x (Or.inl (by rw [hs] at hx; exact hx)))
  have hbound : ∀ x, ‖f x‖ ≤ C.indicator (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]; exact hM x hx
    · rw [Set.indicator_of_notMem hx]
      have : f x = 0 := by
        apply hzero
        by_cases hd : (c, Matrix.of x) ∈ DomR k r z z'
        · right; intro hK; exact hx ((hCmem x).2 ⟨hK, hd.2.1⟩)
        · left; exact hd
      rw [this, norm_zero]
  refine Integrable.mono' ?_ hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  exact (integrable_indicator_iff hCc.measurableSet).mpr
    (integrableOn_const (hμ.finite_compact C hCc).ne)

end Cpt

section Adj

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pairAt_t_adj_cpt' (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ)
    (Φ Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
    (hK : ∃ K : Set (Mx P.k P.r), IsCompact K ∧ K ⊆ {g | 0 < GGl P.k P.r z z' g} ∧
      ∀ g ∈ Glev P.k P.r (Fin.last P.r), g ∉ K →
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = 0)
    (Y : ℂ) (a b : Fin 2) :
    pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c := by
  obtain ⟨K, hKc, hKG, hK0⟩ := hK
  refine pairAt_t_adj_cpt P z z' π π' hP X μ hμ Φ Ψ c hc ⟨K, hKc, hKG, hK0⟩ Y a b (fun m => ?_) (fun m => ?_)
  · exact int_cpt_gen μ hμ Ψ (X.t Y a b Φ) c _ K hKc hKG hc _ (Or.inl rfl) (fun g hg hgK => (hK0 g hg hgK).2)
  · exact int_cpt_gen μ hμ Φ (X.t (star Y) b a Ψ) c _ K hKc hKG hc _ (Or.inr rfl) (fun g hg hgK => (hK0 g hg hgK).1)

end Adj

end Formalism.FourierDecayAlt.P5.HerA
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Cpt

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def CptAt (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  ∃ K : Set (Mx k r), IsCompact K ∧ K ⊆ {g | 0 < GGl k r z z' g} ∧
    ∀ g ∈ Glev k r (Fin.last r), g ∉ K → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0

variable (k r z z' π π') in

def cptSub : Submodule ℂ (RadSp k r z z' π π') where
  carrier := {Φ | ∀ c ∈ OmX r, CptAt Φ c}
  zero_mem' := fun c _ => ⟨∅, isCompact_empty, Set.empty_subset _, fun g _ _ => rfl⟩
  add_mem' := by
    intro Φ Ψ hΦ hΨ c hc
    obtain ⟨K1, h1c, h1G, h10⟩ := hΦ c hc
    obtain ⟨K2, h2c, h2G, h20⟩ := hΨ c hc
    refine ⟨K1 ∪ K2, h1c.union h2c, Set.union_subset h1G h2G, fun g hg hgK => ?_⟩
    show (Φ : Fn k r (Wq →L[ℂ] Wp)) c g + (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
    rw [h10 g hg (fun h => hgK (Or.inl h)), h20 g hg (fun h => hgK (Or.inr h)), add_zero]
  smul_mem' := by
    intro a Φ hΦ c hc
    obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
    refine ⟨K, hKc, hKG, fun g hg hgK => ?_⟩
    show a • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0
    rw [hK0 g hg hgK, smul_zero]

theorem intOn_cpt (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) :
    IntOn μ (cptSub k r z z' π π') := by
  intro c hc Φ hΦ Ψ _
  obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
  simp only [hsInner_eq_sum]
  exact integrable_finsetSum _ fun m _ =>
    int_cpt_gen μ hμ Φ Ψ c _ K hKc hKG hc _ (Or.inr rfl) hK0

theorem smoothLev_slice (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (hc : c ∈ OmX r) (D : Set (Mx k r))
    (hD : D ⊆ {g | 0 < GGl k r z z' g}) :
    SmoothLev k r (Fin.last r) D (fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) := by
  intro g₀ hg₀
  obtain ⟨hg₀G, hg₀D⟩ := hg₀
  obtain ⟨-, hs, -⟩ := Φ.2
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hs (c, g₀)
    (show ((c, g₀) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z' from ⟨hc, hg₀G, hD hg₀D⟩)
  have hcont : Continuous fun g : Mx k r => ((c, g) : (Fin r → ℂ) × Mx k r) := by fun_prop
  have hsm : ContDiff ℝ ∞ fun g : Mx k r => ((c, g) : (Fin r → ℂ) × Mx k r) := by fun_prop
  refine ⟨(fun g : Mx k r => ((c, g) : (Fin r → ℂ) × Mx k r)) ⁻¹' U, fun g => F (c, g), hU.preimage hcont, hxU,
    hF.comp hsm.contDiffOn (fun g hg => hg), ?_⟩
  intro g hg hgG
  exact hΦ (c, g) hg hgG

theorem fn_pres_cpt (X : ActualOps k r z z' π π') (j : Fin 6) :
    ∀ Φ ∈ cptSub k r z z' π π', X.fn j Φ ∈ cptSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
  refine ⟨K, hKc, hKG, fun g hg hgK => ?_⟩
  by_cases hx : ((c, g) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z'
  · have h := X.fn_apply j Φ (c, g) hx
    dsimp only at h
    rw [h, hK0 g hg hgK, smul_zero]
  · obtain ⟨h0, -, -⟩ := (X.fn j Φ).2
    exact h0 (c, g) hx

theorem t_pres_cpt (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) :
    ∀ Φ ∈ cptSub k r z z' π π', X.t Y a b Φ ∈ cptSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨K, hKc, hKG, hK0⟩ := hΦ c hc
  refine ⟨K, hKc, hKG, fun g hg hgK => ?_⟩
  by_cases hd : (c, g) ∈ DomR k r z z'
  · have e := X.t_apply Y a b Φ (c, g) hd
    simp only at e
    rw [e]
    set D : Set (Mx k r) := {g | 0 < GGl k r z z' g} \ K with hDdef
    have hDo : IsOpen D := (isOpen_lt continuous_const (P.Qx5.GGl_continuous k r z z')).sdiff hKc.isClosed
    have hDG : D ⊆ {g | 0 < GGl k r z z' g} := Set.sdiff_subset
    have hgD : g ∈ Glev k r (Fin.last r) ∩ D := ⟨hg, hd.2.2, hgK⟩
    have hS1 := smoothLev_slice Φ c hc D hDG
    have hS0 : SmoothLev k r (Fin.last r) D (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) := by
      intro g₀ hg₀
      exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
    have hL := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
      (fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) (fun _ => 0) 1 hDo hS1 hS0 g hgD
    have hL0 := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
      (fun _ => (0 : Wq →L[ℂ] Wp)) (fun _ => 0) 1 hDo hS0 hS0 g hgD
    have h0 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g = 0 := by
      have h := hL0.1
      simp only [smul_zero, add_zero, one_smul] at h
      have h2 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g +
          tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g =
          tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g + 0 := by
        rw [add_zero]; exact h.symm
      exact add_left_cancel h2
    have hloc := hL.2 (fun x hx => hK0 x hx.1 hx.2.2)
    rw [show (Φ : Fn k r (Wq →L[ℂ] Wp)) c = fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g from rfl, hloc, h0]
  · exact radSp_zero_off (X.t Y a b Φ) (x := (c, g)) hd

end Cpt

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem QQ_mem_adjAlg_cpt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (hP : IsPlace P z z' π π') (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (Y : ℂ) (a b : Fin 2) :
    X.QQ Y a b ∈ adjAlg μ (cptSub P.k P.r z z' π π') (intOn_cpt μ hμ) := by
  refine ⟨t_pres_cpt X Y a b, t_pres_cpt X (star Y) b a, fun c hc Φ hΦ Ψ hΨ => ?_⟩
  show pairAt μ (X.t Y a b Φ) Ψ c = pairAt μ Φ (X.t (star Y) b a Ψ) c
  obtain ⟨K1, h1c, h1G, h10⟩ := hΦ c hc
  obtain ⟨K2, h2c, h2G, h20⟩ := hΨ c hc
  exact pairAt_t_adj_cpt' P z z' π π' hP X μ hμ Φ Ψ c hc
    ⟨K1 ∪ K2, h1c.union h2c, Set.union_subset h1G h2G,
      fun g hg hgK => ⟨h10 g hg (fun h => hgK (Or.inl h)), h20 g hg (fun h => hgK (Or.inr h))⟩⟩ Y a b

theorem adjTop_cpt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (hK : K (Fin.last P.r) ≤ cptSub P.k P.r z z' π π') :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  exact adjTop_of_tAdj (S := S) P z z' π π' X μ L st K l0 hD (cptSub P.k P.r z z' π π') (intOn_cpt μ hD.2.1) hK
    (fn_pres_cpt X) (fun Y _ a b => QQ_mem_adjAlg_cpt P z z' π π' hD.1 X μ hD.2.1 Y a b)

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Form

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

theorem hb_add_left (x y w : Fin m → ℂ) : herm H (x + y) w = herm H x w + herm H y w := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]

theorem hb_sub_left (x y w : Fin m → ℂ) : herm H (x - y) w = herm H x w - herm H y w := by
  simp only [herm, Matrix.mulVec_sub, dotProduct_sub]

theorem hb_smul_left (c : ℂ) (x w : Fin m → ℂ) : herm H (c • x) w = c * herm H x w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hb_add_right (x w w' : Fin m → ℂ) : herm H x (w + w') = herm H x w + herm H x w' := by
  simp only [herm, star_add, add_dotProduct]

theorem hb_sub_right (x w w' : Fin m → ℂ) : herm H x (w - w') = herm H x w - herm H x w' := by
  simp only [herm, star_sub, sub_dotProduct]

theorem hb_smul_right (c : ℂ) (x w : Fin m → ℂ) : herm H x (c • w) = star c * herm H x w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem hb_symm (hH : Hᴴ = H) (x y : Fin m → ℂ) : herm H y x = star (herm H x y) := by
  simp only [herm]
  rw [star_dotProduct, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]

theorem hb_UH {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H) (x y : Fin m → ℂ) :
    herm H (g *ᵥ x) (g *ᵥ y) = herm H x y := by
  have hg' : gᴴ * H * g = H := hg
  simp only [herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem hb_self_real (hH : Hᴴ = H) (x : Fin m → ℂ) : herm H x x = ((herm H x x).re : ℂ) := by
  have h := hb_symm H hH x x
  exact (Complex.conj_eq_iff_re.mp (by simpa [Complex.star_def] using h.symm)).symm

theorem hb_expand (u v : Fin m → ℂ) (s : ℂ) :
    herm H (u + s • v) (u + s • v) =
      herm H u u + star s * herm H u v + s * herm H v u + s * star s * herm H v v := by
  rw [hb_add_left, hb_add_right, hb_add_right, hb_smul_left, hb_smul_left, hb_smul_right,
    hb_smul_right]
  ring

end Form

section Wb

variable {k r : ℕ}

theorem hpk_herm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk]
  rcases i with ⟨a, ha⟩
  rcases j with ⟨b, hb⟩
  simp only [Fin.mk.injEq]
  split_ifs <;> first | (exfalso; omega) | simp

theorem inWb_add {x y : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hy : inWb k r y) : inWb k r (x + y) := by
  intro i hi
  simp only [Pi.add_apply, hx i hi, hy i hi, add_zero]

theorem inWb_sub {x y : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hy : inWb k r y) : inWb k r (x - y) := by
  intro i hi
  simp only [Pi.sub_apply, hx i hi, hy i hi, sub_zero]

theorem inWb_smul (c : ℂ) {x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) : inWb k r (c • x) := by
  intro i hi
  simp only [Pi.smul_apply, hx i hi, smul_zero]

theorem perp_nonneg {b v : Fin (2 * r + k + 1) → ℂ} (hb : inWb k r b) (hbn : (herm (Hpk k r) b b).re < 0)
    (hv : inWb k r v) (hvb : herm (Hpk k r) v b = 0) : 0 ≤ (herm (Hpk k r) v v).re := by
  by_contra hneg
  push_neg at hneg
  have h := reverse_cauchy_schwarz_holds k r v b hv hb hneg hbn
  have h0 : herm (Hpk k r) b v = 0 := by rw [hb_symm _ (hpk_herm k r) v b, hvb, star_zero]
  rw [h0, map_zero] at h
  have h1 : 0 < Tz k r v := by unfold Tz; linarith
  have h2 : 0 < Tz k r b := by unfold Tz; linarith
  nlinarith [mul_pos h1 h2]

theorem norm_perp_le {b u v : Fin (2 * r + k + 1) → ℂ} (hb : inWb k r b) (hbn : (herm (Hpk k r) b b).re < 0)
    (hu : inWb k r u) (hv : inWb k r v) (hub : herm (Hpk k r) u b = 0) (hvb : herm (Hpk k r) v b = 0) :
    ‖herm (Hpk k r) u v‖ ≤ (herm (Hpk k r) u u).re + (herm (Hpk k r) v v).re := by
  set H := Hpk k r
  have hvu : herm H v u = star (herm H u v) := hb_symm H (hpk_herm k r) u v
  have key : ∀ s : ℂ, s * star s = 1 →
      0 ≤ (herm H u u).re + (herm H v v).re + (star s * herm H u v + s * star (herm H u v)).re := by
    intro s hs
    have hw : inWb k r (u + s • v) := inWb_add hu (inWb_smul s hv)
    have hwb : herm H (u + s • v) b = 0 := by rw [hb_add_left, hb_smul_left, hub, hvb]; ring
    have h0 := perp_nonneg hb hbn hw hwb
    rw [hb_expand, hvu, hs, one_mul] at h0
    simp only [Complex.add_re] at h0 ⊢
    linarith
  set X := herm H u v
  have k1 := key 1 (by simp)
  have k2 := key (-1) (by simp)
  have k3 := key Complex.I (by simp [Complex.star_def])
  have k4 := key (-Complex.I) (by simp [Complex.star_def])
  simp only [Complex.star_def, map_one, map_neg, Complex.conj_I, one_mul, neg_mul, neg_neg, Complex.add_re,
    Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, zero_mul,
    one_mul, sub_zero, zero_sub, mul_neg, neg_zero] at k1 k2 k3 k4
  have hre : |X.re| ≤ ((herm H u u).re + (herm H v v).re) / 2 := by
    rw [abs_le]; constructor <;> linarith
  have him : |X.im| ≤ ((herm H u u).re + (herm H v v).re) / 2 := by
    rw [abs_le]; constructor <;> linarith
  calc ‖X‖ ≤ |X.re| + |X.im| := Complex.norm_le_abs_re_add_abs_im X
    _ ≤ _ := by linarith

end Wb

section Bound

variable {k r : ℕ}

theorem hb_sub_expand {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u v w : Fin m → ℂ) (s s' : ℂ) :
    herm H (u - s • w) (v - s' • w) =
      herm H u v - star s' * herm H u w - s * herm H w v + s * star s' * herm H w w := by
  rw [hb_sub_left, hb_sub_right, hb_sub_right, hb_smul_left, hb_smul_left, hb_smul_right,
    hb_smul_right]
  ring

theorem norm_herm_le {a b c : Fin (2 * r + k + 1) → ℂ} (ha : inWb k r a) (hb : inWb k r b) (hc : inWb k r c)
    (hbn : (herm (Hpk k r) b b).re < 0) :
    ‖herm (Hpk k r) a c‖ ≤ (herm (Hpk k r) a a).re + (herm (Hpk k r) c c).re +
      (-(herm (Hpk k r) b b).re)⁻¹ * (‖herm (Hpk k r) a b‖ ^ 2 + ‖herm (Hpk k r) c b‖ ^ 2 +
        ‖herm (Hpk k r) a b‖ * ‖herm (Hpk k r) c b‖) := by
  set H := Hpk k r with hHdef
  have hH : Hᴴ = H := hpk_herm k r
  set T : ℝ := -(herm H b b).re with hTdef
  have hTpos : 0 < T := by rw [hTdef]; linarith
  set t : ℝ := T⁻¹ with htdef
  have htT : (t : ℂ) * (T : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, htdef, inv_mul_cancel₀ hTpos.ne', Complex.ofReal_one]
  have hbb : herm H b b = -(T : ℂ) := by
    rw [hb_self_real H hH b, hTdef]; push_cast; ring
  set X := herm H a b with hX
  set Z := herm H c b with hZ
  have hXn : X * star X = ((‖X‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hZn : Z * star Z = ((‖Z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hst : star (t : ℂ) = (t : ℂ) := by rw [Complex.star_def, Complex.conj_ofReal]
  set α : ℂ := -((t : ℂ) * X) with hα
  set γ : ℂ := -((t : ℂ) * Z) with hγ
  have hsα : star α = -((t : ℂ) * star X) := by rw [hα, star_neg, star_mul', hst]
  have hsγ : star γ = -((t : ℂ) * star Z) := by rw [hγ, star_neg, star_mul', hst]
  have hba : herm H b a = star X := hb_symm H hH a b
  have hbc : herm H b c = star Z := hb_symm H hH c b
  have ha' : inWb k r (a - α • b) := inWb_sub ha (inWb_smul α hb)
  have hc' : inWb k r (c - γ • b) := inWb_sub hc (inWb_smul γ hb)
  have ha'b : herm H (a - α • b) b = 0 := by
    rw [hb_sub_left, hb_smul_left, hbb, ← hX, hα]
    linear_combination (-X) * htT
  have hc'b : herm H (c - γ • b) b = 0 := by
    rw [hb_sub_left, hb_smul_left, hbb, ← hZ, hγ]
    linear_combination (-Z) * htT
  have eac := hb_sub_expand H a c b α γ
  rw [← hX, hbc, hsγ, hbb] at eac
  have eaa := hb_sub_expand H a a b α α
  rw [← hX, hba, hsα, hbb] at eaa
  have ecc := hb_sub_expand H c c b γ γ
  rw [← hZ, hbc, hsγ, hbb] at ecc
  have hac : herm H a c = herm H (a - α • b) (c - γ • b) - (t : ℂ) * X * star Z := by
    rw [eac, hα]
    linear_combination ((t : ℂ) * X * star Z) * htT
  have haa' : herm H (a - α • b) (a - α • b) = herm H a a + ((t * ‖X‖ ^ 2 : ℝ) : ℂ) := by
    rw [eaa, hα]; push_cast at hXn ⊢
    linear_combination ((2 : ℂ) * t - t * t * T) * hXn + (-(t * ‖X‖ ^ 2 : ℂ)) * htT
  have hcc' : herm H (c - γ • b) (c - γ • b) = herm H c c + ((t * ‖Z‖ ^ 2 : ℝ) : ℂ) := by
    rw [ecc, hγ]; push_cast at hZn ⊢
    linear_combination ((2 : ℂ) * t - t * t * T) * hZn + (-(t * ‖Z‖ ^ 2 : ℂ)) * htT
  have hperp := norm_perp_le hb hbn ha' hc' ha'b hc'b
  rw [haa', hcc', Complex.add_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re] at hperp
  have ht0 : 0 ≤ t := inv_nonneg.mpr hTpos.le
  have hn : ‖(t : ℂ) * X * star Z‖ = t * (‖X‖ * ‖Z‖) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, norm_star]; ring
  rw [hac]
  calc ‖herm H (a - α • b) (c - γ • b) - (t : ℂ) * X * star Z‖
      ≤ ‖herm H (a - α • b) (c - γ • b)‖ + ‖(t : ℂ) * X * star Z‖ := norm_sub_le _ _
    _ ≤ _ := by rw [hn]; nlinarith

end Bound

section Group

variable {k r : ℕ}

theorem hpk_outer (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    (Hpk k r *ᵥ y) ⟨2 * r + k - i.val, by omega⟩ = y i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · simp only [Hpk, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | simp
  · intro j _ hj
    have hj' : j.val ≠ i.val := fun h => hj (Fin.ext h)
    simp only [Hpk, Fin.val_mk, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · simp

theorem norm_hpk_mid (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val ∧ i.val ≤ r + k) :
    ‖(Hpk k r *ᵥ y) i‖ = ‖y i‖ := by
  have h : (Hpk k r *ᵥ y) i = (if i.val = r + k then -1 else 1) * y i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · simp only [Hpk, and_true]
      split_ifs <;> first | (exfalso; omega) | simp
    · intro j _ hj
      have hj' : j.val ≠ i.val := fun h => hj (Fin.ext h)
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | simp
    · simp
  rw [h]
  split_ifs <;> simp

theorem glev_fix {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (q : Fin (2 * r + k + 1))
    (hq : q.val < r ∨ r + k < q.val) : g *ᵥ bvec q = bvec q := by
  rcases hq with hq | hq
  · have e : q = eI k r ⟨q.val, hq⟩ := Fin.ext rfl
    rw [e]
    exact (hg.2 ⟨q.val, hq⟩ (by simp only [Fin.val_last]; exact hq)).1
  · have hlt : 2 * r + k - q.val < r := by omega
    have e : q = esI k r ⟨2 * r + k - q.val, hlt⟩ := Fin.ext (by simp only [esI]; omega)
    rw [e]
    exact (hg.2 ⟨2 * r + k - q.val, hlt⟩ (by simp only [Fin.val_last]; exact hlt)).2

theorem glev_wb {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (g *ᵥ v) := by
  intro i hi
  have hp := hpk_outer (g *ᵥ v) i hi
  have hp' := hpk_outer v i hi
  have hout : (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val < r ∨
      r + k < (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val := by simp only [Fin.val_mk]; omega
  rw [← hp, ← gn_herm_bvec_right, ← glev_fix hg _ hout, hb_UH _ hg.1, gn_herm_bvec_right, hp', hv i hi]

theorem bvec_wb (q : Fin (2 * r + k + 1)) (hq : r ≤ q.val ∧ q.val ≤ r + k) : inWb k r (bvec q) := by
  intro i hi
  have hne : i ≠ q := by
    rintro rfl
    omega
  simp [bvec, Pi.single_apply, hne]

theorem entry_eq (g : Mx k r) (p q : Fin (2 * r + k + 1)) : g p q = (g *ᵥ bvec q) p := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

variable (z z' : Fin (2 * r + k + 1) → ℂ)

def bz (p : Fin (2 * r + k + 1)) (R : ℝ) : ℝ :=
  (herm (Hpk k r) (bvec p) (bvec p)).re + (herm (Hpk k r) z' z').re +
    (-(herm (Hpk k r) z z).re)⁻¹ * (‖herm (Hpk k r) (bvec p) z‖ ^ 2 + R ^ 2 + ‖herm (Hpk k r) (bvec p) z‖ * R)

def bnd (p q : Fin (2 * r + k + 1)) (R : ℝ) : ℝ :=
  1 + |(herm (Hpk k r) (bvec q) (bvec q)).re| + |(herm (Hpk k r) (bvec p) (bvec p)).re| +
    (-(herm (Hpk k r) z' z').re)⁻¹ * (‖herm (Hpk k r) (bvec q) z'‖ ^ 2 + bz z z' p R ^ 2 +
      ‖herm (Hpk k r) (bvec q) z'‖ * |bz z z' p R|)

theorem one_le_bnd (hT' : 0 < Tz k r z') (p q : Fin (2 * r + k + 1)) (R : ℝ) : 1 ≤ bnd z z' p q R := by
  unfold bnd
  have h0 : 0 ≤ (-(herm (Hpk k r) z' z').re)⁻¹ := inv_nonneg.mpr (le_of_lt hT')
  have h1 : 0 ≤ (-(herm (Hpk k r) z' z').re)⁻¹ * (‖herm (Hpk k r) (bvec q) z'‖ ^ 2 + bz z z' p R ^ 2 +
      ‖herm (Hpk k r) (bvec q) z'‖ * |bz z z' p R|) := mul_nonneg h0 (by positivity)
  have h2 := abs_nonneg (herm (Hpk k r) (bvec q) (bvec q)).re
  have h3 := abs_nonneg (herm (Hpk k r) (bvec p) (bvec p)).re
  linarith

theorem norm_herm_gz_le (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (R : ℝ) (hR : ‖zetaL k r z z' (Fin.last r) g‖ ≤ R)
    (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    ‖herm (Hpk k r) (bvec p) (g *ᵥ z')‖ ≤ bz z z' p R := by
  have hzn : (herm (Hpk k r) z z).re < 0 := by unfold Tz at hT; linarith
  have h := norm_herm_le (bvec_wb p hp) hz (glev_wb hg hz') hzn
  rw [hb_UH _ hg.1] at h
  have hζ : herm (Hpk k r) (g *ᵥ z') z = zetaL k r z z' (Fin.last r) g := by
    simp only [zetaL, fvec_last]
  rw [hζ] at h
  unfold bz
  have h0 : 0 ≤ (-(herm (Hpk k r) z z).re)⁻¹ := inv_nonneg.mpr (by linarith)
  have hn0 := norm_nonneg (zetaL k r z z' (Fin.last r) g)
  have hsq : ‖zetaL k r z z' (Fin.last r) g‖ ^ 2 ≤ R ^ 2 := by nlinarith
  have hm : ‖herm (Hpk k r) (bvec p) z‖ * ‖zetaL k r z z' (Fin.last r) g‖ ≤
      ‖herm (Hpk k r) (bvec p) z‖ * R := mul_le_mul_of_nonneg_left hR (norm_nonneg _)
  have := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (le_refl (‖herm (Hpk k r) (bvec p) z‖ ^ 2)) hsq) hm) h0
  linarith

theorem norm_entry_le (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (R : ℝ) (hR : ‖zetaL k r z z' (Fin.last r) g‖ ≤ R)
    (p q : Fin (2 * r + k + 1)) : ‖g p q‖ ≤ bnd z z' p q R := by
  have h1 := one_le_bnd z z' hT' p q R
  rw [entry_eq g p q]
  by_cases hq : q.val < r ∨ r + k < q.val
  · rw [glev_fix hg q hq]
    by_cases hpq : p = q
    · subst hpq; simp [bvec]; linarith
    · simp [bvec, Pi.single_apply, hpq]; linarith
  have hq' : r ≤ q.val ∧ q.val ≤ r + k := by omega
  by_cases hp : p.val < r ∨ r + k < p.val
  · rw [glev_wb hg (bvec_wb q hq') p hp, norm_zero]; linarith
  have hp' : r ≤ p.val ∧ p.val ≤ r + k := by omega
  have hz'n : (herm (Hpk k r) (g *ᵥ z') (g *ᵥ z')).re < 0 := by
    rw [hb_UH _ hg.1]; unfold Tz at hT'; linarith
  rw [← norm_hpk_mid _ p hp', ← gn_herm_bvec_right]
  have h := norm_herm_le (glev_wb hg (bvec_wb q hq')) (glev_wb hg hz') (bvec_wb p hp') hz'n
  rw [hb_UH _ hg.1, hb_UH _ hg.1, hb_UH _ hg.1] at h
  have hb := norm_herm_gz_le z z' hz hz' hT hg R hR p hp'
  have hbabs : ‖herm (Hpk k r) (bvec p) (g *ᵥ z')‖ ≤ |bz z z' p R| := hb.trans (le_abs_self _)
  have h0 : 0 ≤ (-(herm (Hpk k r) z' z').re)⁻¹ := inv_nonneg.mpr (by unfold Tz at hT'; linarith)
  have hn0 := norm_nonneg (herm (Hpk k r) (bvec p) (g *ᵥ z'))
  have hsq : ‖herm (Hpk k r) (bvec p) (g *ᵥ z')‖ ^ 2 ≤ bz z z' p R ^ 2 := by
    have := abs_nonneg (bz z z' p R)
    nlinarith [sq_abs (bz z z' p R)]
  have hm := mul_le_mul_of_nonneg_left hbabs (norm_nonneg (herm (Hpk k r) (bvec q) z'))
  have := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (le_refl (‖herm (Hpk k r) (bvec q) z'‖ ^ 2)) hsq) hm) h0
  unfold bnd
  have := le_abs_self (herm (Hpk k r) (bvec q) (bvec q)).re
  have := le_abs_self (herm (Hpk k r) (bvec p) (bvec p)).re
  linarith

theorem isCompact_zeta_le (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (ε R : ℝ) :
    IsCompact {g : Mx k r | g ∈ Glev k r (Fin.last r) ∧ ε ≤ GGl k r z z' g ∧
      ‖zetaL k r z z' (Fin.last r) g‖ ≤ R} := by
  have hbox : IsCompact (Set.pi Set.univ fun p : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun q : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) (bnd z z' p q R)) :=
    isCompact_univ_pi fun p => isCompact_univ_pi fun q => isCompact_closedBall _ _
  have hcl : IsClosed {g : Mx k r | g ∈ Glev k r (Fin.last r) ∧ ε ≤ GGl k r z z' g ∧
      ‖zetaL k r z z' (Fin.last r) g‖ ≤ R} :=
    (Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).inter
      ((isClosed_le continuous_const (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous k r z z')).inter
        (isClosed_le (continuous_norm.comp (Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff k r z z' (Fin.last r)).continuous)
          continuous_const))
  refine hbox.of_isClosed_subset hcl ?_
  rintro g ⟨hg, -, hR⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun p q => norm_entry_le z z' hz hz' hT hT' hg R hR p q

end Group

end Formalism.FourierDecayAlt.P5.HerB
end
end
