import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.InfinitePlaceDepthSums
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.FreeLiftMetric

open Module NumberField IsDedekindDomain
open scoped Matrix MatrixOrder ComplexOrder
open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.PairingDivisionLocalBalance Formalism.HN GlobalTheory.IndefiniteRowSideFullHecke.InfinitePlaceDepthSums

noncomputable section

namespace GlobalTheory.Proof.DualMatrixMetricMeans

section Mat
open scoped Matrix.Norms.L2Operator

theorem opNorm_eq_of_gram {n p q : Type} [Fintype n] [Fintype p] [Fintype q] [DecidableEq n] [DecidableEq p]
    [DecidableEq q] (B : Matrix n p ℂ) (B' : Matrix n q ℂ) (h : B * Bᴴ = B' * B'ᴴ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B)‖ =
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B')‖ := by
  change ‖B‖ = ‖B'‖
  have h1 := Matrix.l2_opNorm_conjTranspose_mul_self Bᴴ
  have h2 := Matrix.l2_opNorm_conjTranspose_mul_self B'ᴴ
  rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h1 h2
  rw [h, h2] at h1
  exact ((mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 h1).symm

end Mat

theorem frame_gram {n : Type} [Fintype n] [DecidableEq n] (X G : Matrix n n ℂ) (hX : IsUnit X.det)
    (h : (X⁻¹)ᴴ * X⁻¹ = G) : X * Xᴴ = G⁻¹ := by
  rw [← h, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hX, ← Matrix.conjTranspose_nonsing_inv,
    Matrix.nonsing_inv_nonsing_inv _ hX]

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def SameMetric {a : ℕ} (X' XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) : Prop :=
  ∀ v, (X' v)⁻¹ = (dualFrame XM v)⁻¹

def dualMat {n a : ℕ} (vm : (Fin n → K) →ₗ[K] Module.Dual K (Fin a → K)) : Matrix (Fin a) (Fin n) K :=
  LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin a)).dualBasis vm


theorem opNormAt_quot (hW : Df.WF) {a : ℕ} {X' XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ} (hX : SameMetric X' XM)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (vb : Matrix (Fin a) (Fin (Df.dQ Bs.μ0)) K) (hvb : vb * Df.Pq Bs.μ0 = dualMat vm) (v : InfinitePlace K) :
    opNormAt (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) (Pi.basisFun K (Fin a)) X' v (Matrix.mulVecLin vb) =
      opNormAt (Pi.basisFun K (Fin (Df.nV Bs.μ0))) (formFrame (Df.HV Bs.μ0))
        (Pi.basisFun K (Fin a)).dualBasis (dualFrame XM) v vm := by
  unfold opNormAt
  have e1 : LinearMap.toMatrix (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Pi.basisFun K (Fin a)) (Matrix.mulVecLin vb) = vb := by
    ext i j; simp [LinearMap.toMatrix_apply]
  have e2 : LinearMap.toMatrix (Pi.basisFun K (Fin (Df.nV Bs.μ0))) (Pi.basisFun K (Fin a)).dualBasis vm =
      vb * Df.Pq Bs.μ0 := hvb.symm
  rw [e1, e2, ← hX v, Matrix.map_mul]
  obtain ⟨hQ, hQG⟩ := hW.XQ_quot Bs.μ0 v
  obtain ⟨hV, hVG⟩ := formFrame_spec (Df.HV Bs.μ0) v (hW.HV_pos Bs.μ0 v)
  have gQ := frame_gram _ _ hQ hQG
  have gV := frame_gram _ _ hV hVG
  set G := (Df.Pq Bs.μ0).map v.embedding * ((Df.HV Bs.μ0).map v.embedding)⁻¹ * ((Df.Pq Bs.μ0).map v.embedding)ᴴ
    with hG
  have hGu : IsUnit G.det := by
    have h1 : IsUnit G⁻¹ := by
      rw [← hQG]
      have := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hQ)
      exact ((Matrix.isUnit_conjTranspose _).2 this).mul this
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_nonsing_inv_iff.1 h1)
  rw [Matrix.nonsing_inv_nonsing_inv _ hGu] at gQ
  apply opNorm_eq_of_gram
  set A := (X' v)⁻¹ * vb.map v.embedding
  set P := (Df.Pq Bs.μ0).map v.embedding
  set XV := formFrame (Df.HV Bs.μ0) v
  set XQ := Df.XQ Bs.μ0 v
  have e3 : (X' v)⁻¹ * (vb.map v.embedding * P) * XV = A * (P * XV) := by simp only [A, Matrix.mul_assoc]
  rw [e3]
  calc A * XQ * (A * XQ)ᴴ = A * (XQ * XQᴴ) * Aᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = A * (P * (XV * XVᴴ) * Pᴴ) * Aᴴ := by rw [gQ, gV]
    _ = A * (P * XV) * (A * (P * XV))ᴴ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem meanInf_eq [IsTotallyComplex K] (g : InfinitePlace K → ℝ) :
    meanInf K g = (1 / (nPl K : ℝ)) * ∑ v, g v := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  unfold meanInf
  rw [Formalism.HN.twist_finrank_eq K]
  field_simp

theorem meanInf_mono {g g' : InfinitePlace K → ℝ} (h : ∀ v, g v ≤ g' v) : meanInf K g ≤ meanInf K g' :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => h v) (by positivity)

theorem meanInf_const [IsTotallyComplex K] (c : ℝ) : meanInf K (fun _ => c) = c := by
  have hn : (nPl K : ℝ) ≠ 0 := by
    have := Formalism.HN.twist_finrank_eq K
    have h0 : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    intro h; rw [h] at this; linarith
  rw [meanInf_eq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change 1 / (nPl K : ℝ) * ((nPl K : ℝ) * c) = c
  field_simp

theorem htMap_quot [IsTotallyComplex K] (hW : Df.WF) {a : ℕ} {X' XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ}
    (hX : SameMetric X' XM) (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K))
    (vb : Matrix (Fin a) (Fin (Df.dQ Bs.μ0)) K) (hvb : vb * Df.Pq Bs.μ0 = dualMat vm) :
    htMap (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) (Pi.basisFun K (Fin a)) X' (Matrix.mulVecLin vb) =
      meanInf K (logNormV_sq Df XM vm) := by
  rw [meanInf_eq]
  unfold htMap logNormV_sq
  simp only [opNormAt_quot hW hX vm vb hvb]


theorem exists_lower_iff (hW : Df.WF) (S : IndefRows Df) (c : ℝ) :
    (∃ g : InfinitePlace K → ℝ, (∀ v p, Df.Qp Bs.μ0 p ≠ ⊥ → g v ≤ ∑ j, Real.log (S.lam j Bs.μ0 p v)) ∧
      c ≤ meanInf K g) ↔ c ≤ meanInf K (lamMin hW S) := by
  classical
  constructor
  · rintro ⟨g, hg, hc⟩
    exact hc.trans (meanInf_mono fun v => le_lamMin hW S v _ (hg v))
  · intro h
    refine ⟨lamMin hW S, fun v p hp => ?_, h⟩
    exact Finset.inf'_le (fun p => ∑ j, Real.log (S.lam j Bs.μ0 p v)) (by simpa [occurring] using hp)

def LinTie (O : FunData K Df) (XM : InfinitePlace K → Matrix (Fin O.n) (Fin O.n) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin O.n → K)) : Prop :=
  SameMetric O.X' XM ∧ O.vmu Bs.μ0 = dualMat vm




def NumTie (O : FunData K Df) (E : Type) [Field E] [NumberField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
    (e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ) (C b : ℝ) : Prop :=
  O.f = numF E ∧ O.m = Fintype.card Bs.J ∧
    ∃ φ : O.Sq → HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      Set.BijOn φ O.S0 S0 ∧ ∀ q ∈ O.S0, O.qq q = Ideal.absNorm (φ q).asIdeal ∧ e (φ q) = O.ee C b q

theorem NumTie.sig {O : FunData K Df} {E : Type} [Field E] [NumberField E]
    {S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E)))}
    {e : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ} {C b : ℝ} (h : NumTie O E S0 e C b) :
    depthSum S0 e = O.Sig0 C b := by
  obtain ⟨-, -, φ, hφ, hq⟩ := h
  unfold depthSum FunData.Sig0
  symm
  refine Finset.sum_nbij φ (fun q hq' => hφ.mapsTo hq') hφ.injOn hφ.surjOn fun q hq' => ?_
  rw [(hq q hq').1, (hq q hq').2]







open Classical in

def recordOf (Df : DefSide Bs) {a : ℕ} (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
    (vm : (Fin (Df.nV Bs.μ0) → K) →ₗ[K] Module.Dual K (Fin a → K)) (E : Type) [Field E] [NumberField E]
    (S0 : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E)))) (v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (k t g₁ g₂ p p' : ℕ) : FunData K Df where
  n := a
  X' := dualFrame XM
  M := ⊥
  vmu := Function.update (fun _ => 0) Bs.μ0 (dualMat vm)
  Tf := ∅
  dF := 0
  m := Fintype.card Bs.J
  rq := fun _ _ => 1
  dl := 0
  Sd := ∅
  Se := ∅
  N0 := 0
  zA := 0
  zA' := 0
  zT := 0
  zTd := 0
  gT := 0
  ch := fun _ => true
  dd := 0
  hd := 0
  yy := 0
  Sq := HeightOneSpectrum (𝓞 (maximalRealSubfield E))
  S0 := S0
  sv0 := v₀
  cc := 0
  qq := fun v => Ideal.absNorm v.asIdeal
  f := numF E
  k := k
  tt := t
  cl := 0
  g1 := g₁
  g2 := g₂
  pd := p
  pd' := p'
  dE := discr E
  Bw := 0






example : IsCMField (CyclotomicField 3 ℚ) := IsCyclotomicExtension.Rat.isCMField (S := {3}) _ ⟨3, rfl, by norm_num⟩

end GlobalTheory.Proof.DualMatrixMetricMeans
