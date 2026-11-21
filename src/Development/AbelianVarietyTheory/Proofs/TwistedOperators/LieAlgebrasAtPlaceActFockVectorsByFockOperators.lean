import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLieActionThroughWeylAlgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTraceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameExistsSignCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BoundedCommutantVacua

section
noncomputable section

namespace GlobalTheory.OnePlaceFock

section Laws

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix Complex
open GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars GlobalTheory.VacuumFockLaws
open GlobalTheory.Ker (ipO)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.ArchRec (IsFrameOf Mn)
open scoped Classical ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fockIp_eq {ι : Type} (P Q : MvPolynomial ι ℂ) :
    fockIp P Q = ∑ k ∈ Q.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) := by
  classical
  have hP : ∀ k ∉ P.support, P.coeff k = 0 := fun k hk => by
    simpa only [MvPolynomial.mem_support_iff, not_not] using hk
  have hQ : ∀ k ∉ Q.support, Q.coeff k = 0 := fun k hk => by
    simpa only [MvPolynomial.mem_support_iff, not_not] using hk
  change ∑ k ∈ P.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) = _
  have hL : ∑ k ∈ P.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) =
      ∑ k ∈ P.support ∪ Q.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro k _ hk
    rw [hP k hk, zero_mul, zero_mul]
  have hR : ∑ k ∈ Q.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) =
      ∑ k ∈ P.support ∪ Q.support, P.coeff k * conj (Q.coeff k) * (multiFact k : ℂ) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro k _ hk
    rw [hQ k hk, map_zero, mul_zero, zero_mul]
  rw [hL, hR]

def sgn {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℝ := if ε a then 1 else -1

theorem sgn_cases {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : sgn ε a = 1 ∨ sgn ε a = -1 := by
  unfold sgn
  by_cases h : ε a
  · left; simp [h]
  · right; simp [h]

theorem Jm_eq_sgn {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε = diagonal fun a => (sgn ε a : ℂ) := by
  unfold Formalism.REAL.Jm
  congr 1
  funext a
  unfold sgn
  by_cases h : ε a <;> simp [h]

theorem frame_inv {n : ℕ} {G s fr : Mn n} {ε : Fin n → Bool} (h : IsFrameOf G s ε fr) :
    IsUnit (fr⁻¹).det ∧ s * fr⁻¹ = fr⁻¹ * diagonal (fun a => (sgn ε a : ℂ)) ∧
      (fr⁻¹)ᴴ * G * fr⁻¹ = diagonal fun a => (sgn ε a : ℂ) := by
  obtain ⟨hu, hG, hs⟩ := h
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hu
  refine ⟨Matrix.isUnit_nonsing_inv_det fr hd, ?_, ?_⟩
  · rw [hs, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Jm_eq_sgn]
  · have e1 : (fr⁻¹)ᴴ * frᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
    rw [← hG]
    calc (fr⁻¹)ᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * fr⁻¹
        = ((fr⁻¹)ᴴ * frᴴ) * Formalism.REAL.Jm ε * (fr * fr⁻¹) := by simp only [Matrix.mul_assoc]
      _ = diagonal fun a => (sgn ε a : ℂ) := by
        rw [e1, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one, Jm_eq_sgn]

private theorem cplxO_unitMap_eq_I_mul_sign_smul {m n : ℕ} {s B : Matrix (Fin n) (Fin n) ℂ} {s' B' : Matrix (Fin m) (Fin m) ℂ}
    {ε : Fin n → ℝ} {ε' : Fin m → ℝ} (hB : IsUnit B.det) (hs : s * B = B * diagonal fun a => (ε a : ℂ))
    (hs' : s' * B' = B' * diagonal fun a => (ε' a : ℂ)) (i : Fin m) (j : Fin n) :
    cplxO s s' (unitMap B B' i j) = (Complex.I * ((ε' i * ε j : ℝ) : ℂ)) • unitMap B B' i j := by
  have hBi : B⁻¹ * s = (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * s * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
      _ = B⁻¹ * (s * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by
        rw [hs, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul]
  have hd : (diagonal fun a => (ε' a : ℂ)) * single i j (1 : ℂ) * (diagonal fun a => (ε a : ℂ)) =
      ((ε' i * ε j : ℝ) : ℂ) • single i j (1 : ℂ) := by
    ext a b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases ha : i = a
    · by_cases hb : j = b
      · subst ha hb; simp
      · simp [hb]
    · simp [ha]
  calc cplxO s s' (unitMap B B' i j)
      = Complex.I • (B' * ((diagonal fun a => (ε' a : ℂ)) * (single i j (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ) *
          (diagonal fun a => (ε a : ℂ))) * B⁻¹) := by
        unfold Formalism.IndefR.Datum.cplxO Formalism.IndefR.Datum.unitMap
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← hBi, ← Matrix.mul_assoc s' B', hs', Matrix.mul_assoc]
    _ = (Complex.I * ((ε' i * ε j : ℝ) : ℂ)) • unitMap B B' i j := by
        rw [hd, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
        rfl

private theorem inv_eq_mul_diagonal_sign_mul_conjTranspose {n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → ℝ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hB : IsUnit B.det) (hG : Bᴴ * G * B = diagonal fun a => (ε a : ℂ)) :
    G⁻¹ = B * (diagonal fun a => (ε a : ℂ)) * Bᴴ := by
  have hdd : (diagonal fun a => (ε a : ℂ)) * (diagonal fun a => (ε a : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h <;> simp [h]
  have e : Bᴴ * G = (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by
    calc Bᴴ * G = Bᴴ * G * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
      _ = Bᴴ * G * B * B⁻¹ := by rw [← Matrix.mul_assoc]
      _ = _ := by rw [hG]
  apply Matrix.inv_eq_left_inv
  calc B * (diagonal fun a => (ε a : ℂ)) * Bᴴ * G = B * (diagonal fun a => (ε a : ℂ)) * (Bᴴ * G) :=
        Matrix.mul_assoc _ _ _
    _ = B * ((diagonal fun a => (ε a : ℂ)) * (diagonal fun a => (ε a : ℂ))) * B⁻¹ := by
        rw [e]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hdd, Matrix.mul_one, Matrix.mul_nonsing_inv _ hB]

private theorem trace_inv_gram_conjTranspose_conj_eq_sign_trace {m n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {G' B' : Matrix (Fin m) (Fin m) ℂ}
    {ε : Fin n → ℝ} {ε' : Fin m → ℝ} (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hB : IsUnit B.det)
    (hG : Bᴴ * G * B = diagonal fun a => (ε a : ℂ)) (hG' : B'ᴴ * G' * B' = diagonal fun a => (ε' a : ℂ))
    (X Y : Matrix (Fin m) (Fin n) ℂ) :
    (G⁻¹ * (B' * Y * B⁻¹)ᴴ * G' * (B' * X * B⁻¹)).trace =
      ((diagonal fun a => (ε a : ℂ)) * Yᴴ * (diagonal fun a => (ε' a : ℂ)) * X).trace := by
  have h1 : Bᴴ * (B⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hB, Matrix.conjTranspose_one]
  rw [inv_eq_mul_diagonal_sign_mul_conjTranspose hε hB hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  have step : B * (diagonal fun a => (ε a : ℂ)) * Bᴴ * ((B⁻¹)ᴴ * (Yᴴ * B'ᴴ)) * G' * (B' * X * B⁻¹) =
      B * ((diagonal fun a => (ε a : ℂ)) * Yᴴ * (B'ᴴ * G' * B') * X) * B⁻¹ := by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (B * (diagonal fun a => (ε a : ℂ))) Bᴴ (B⁻¹)ᴴ, h1, Matrix.mul_one]
  rw [step, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul, hG']

private theorem trace_diagonal_single_conjTranspose_single {m n : ℕ} (ε : Fin n → ℝ) (ε' : Fin m → ℝ) (i i' : Fin m) (j j' : Fin n) :
    ((diagonal fun a => (ε a : ℂ)) * (single i' j' (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ)ᴴ *
      (diagonal fun a => (ε' a : ℂ)) * (single i j (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ)).trace =
      if (i, j) = (i', j') then ((ε' i * ε j : ℝ) : ℂ) else 0 := by
  have hY : (single i' j' (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ)ᴴ = single j' i' 1 := by
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : j' = a <;> by_cases h2 : i' = b <;> simp [h1, h2]
  have hD : (diagonal fun a => (ε a : ℂ)) * (single j' i' (1 : ℂ) : Matrix (Fin n) (Fin m) ℂ) *
      (diagonal fun a => (ε' a : ℂ)) = single j' i' ((ε j' : ℂ) * ε' i') := by
    ext a b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    by_cases h1 : j' = a <;> by_cases h2 : i' = b <;> simp [h1, h2]
  rw [hY, hD, Matrix.trace_single_mul, Matrix.single_apply, smul_eq_mul]
  by_cases h : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := h
    simp [mul_comm]
  · have h' : ¬ (i, j) = (i', j') := fun e => h ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
    simp [h, h']

private theorem trace_inv_gram_single_conj_eq_ite_sign {m n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {G' B' : Matrix (Fin m) (Fin m) ℂ}
    {ε : Fin n → ℝ} {ε' : Fin m → ℝ} (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hB : IsUnit B.det)
    (hG : Bᴴ * G * B = diagonal fun a => (ε a : ℂ)) (hG' : B'ᴴ * G' * B' = diagonal fun a => (ε' a : ℂ))
    (k l : Fin m × Fin n) :
    (G⁻¹ * (B' * (single l.1 l.2 (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ) * B⁻¹)ᴴ * G' *
      (B' * (single k.1 k.2 (1 : ℂ) : Matrix (Fin m) (Fin n) ℂ) * B⁻¹)).trace =
      if k = l then ((ε' k.1 * ε k.2 : ℝ) : ℂ) else 0 := by
  rw [trace_inv_gram_conjTranspose_conj_eq_sign_trace hε hB hG hG', trace_diagonal_single_conjTranspose_single]

private theorem exists_end_coe_eq_of_linear_on_submodule {X : Type*} (M : Submodule ℂ (X → ℂ)) (T : (X → ℂ) → (X → ℂ))
    (hmem : ∀ g ∈ M, T g ∈ M) (hadd : ∀ g ∈ M, ∀ h ∈ M, T (g + h) = T g + T h)
    (hsmul : ∀ (c : ℂ), ∀ g ∈ M, T (c • g) = c • T g) :
    ∃ a : Module.End ℂ M, ∀ g : M, (a g : X → ℂ) = T g :=
  ⟨{ toFun := fun g => ⟨T g, hmem g g.2⟩
     map_add' := fun g h => Subtype.ext (hadd g g.2 h h.2)
     map_smul' := fun c g => Subtype.ext (hsmul c g g.2) }, fun _ => rfl⟩

set_option maxHeartbeats 4000000 in
private theorem laws_lemma_7 {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) {s B : Mn V.rank} {s' B' : Mn W.rank} {ε : Fin V.rank → ℝ} {ε' : Fin W.rank → ℝ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hε' : ∀ a, ε' a = 1 ∨ ε' a = -1) (hB : IsUnit B.det)
    (hs : s * B = B * diagonal fun a => (ε a : ℂ)) (hs' : s' * B' = B' * diagonal fun a => (ε' a : ℂ))
    (hG : Bᴴ * gramAt D V τ * B = diagonal fun a => (ε a : ℂ))
    (hG' : B'ᴴ * gramAt D W τ * B' = diagonal fun a => (ε' a : ℂ)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hvac : IsFockVacAt (heisO ψ V W) θ τ (cplxO s s') f) :
    (∀ P, IsThetaFunO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P)) ∧
      (f ≠ 0 → Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f)) ∧
      ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
        ∀ P Q, ipO μ 𝓕 (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f Q) =
          ipO μ 𝓕 f f * fockIp P Q := by
  classical
  have hsk := GlobalTheory.ThetaSquare.derSkew (V := V) (W := W) hψ hθ
  have hco := GlobalTheory.ThetaSquare.derComm (V := V) (W := W) hψ hθ
  have hsq := GlobalTheory.VacuumFockLaws.fockScale_sq (D := D) τ
  have hc0 := GlobalTheory.VacuumFockLaws.fockScale_ne (D := D) τ
  have hcinv : (fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ * (8 * Real.pi * ((tauE D τ D.host.xi0).im : ℂ)) = 1 := by
    rw [← hsq]
    field_simp
  have hconj : (starRingEnd ℂ) (fockScale D τ : ℂ)⁻¹ = (fockScale D τ : ℂ)⁻¹ := by rw [map_inv₀, Complex.conj_ofReal]
  have hconjE : (starRingEnd ℂ) (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) = -(-((fockScale D τ : ℂ)⁻¹ * Complex.I)) := by
    rw [map_neg, map_mul, hconj, Complex.conj_I]
    ring
  have Dth : ∀ z g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g) := fun z g hg => (hsk τ z).2.1 g hg
  have Dlin : ∀ z (α β : ℂ) F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G →
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (α • F + β • G) = α • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z F + β • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z G := by
    intro z α β F G hF hG
    rw [GlobalTheory.Size.dRho_add hψ hθ τ z (GlobalTheory.OrientedHeis.theta_smul α hF) (GlobalTheory.OrientedHeis.theta_smul β hG),
      GlobalTheory.Size.dRho_smul, GlobalTheory.Size.dRho_smul]
  have Cm : ∀ z w g, IsThetaFunO ψ V W g → ∀ x,
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ w g) x = Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ w (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g) x + GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.commScalar V W τ τ z w * g x := by
    intro z w g hg x
    have e := congrFun ((hco τ τ z w).2 g hg) x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    linear_combination e
  have hJ : ∀ k : Fin W.rank × Fin V.rank, cplxO s s' (unitMap B B' k.1 k.2) = ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) :=
    fun k => cplxO_unitMap_eq_I_mul_sign_smul hB hs hs' k.1 k.2
  have hσ : ∀ k : Fin W.rank × Fin V.rank, (ε' k.1 * ε k.2) * (ε' k.1 * ε k.2) = 1 := by
    intro k
    rcases hε k.2 with h | h <;> rcases hε' k.1 with h' | h' <;> rw [h, h'] <;> norm_num
  have htr : ∀ (α β : ℂ) (k l : Fin W.rank × Fin V.rank),
      ((gramAt D V τ)⁻¹ * (β • unitMap B B' l.1 l.2)ᴴ * gramAt D W τ * (α • unitMap B B' k.1 k.2)).trace =
        α * ((starRingEnd ℂ) β * (if k = l then ((ε' k.1 * ε k.2 : ℝ) : ℂ) else 0)) := by
    intro α β k l
    rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, ← trace_inv_gram_single_conj_eq_ite_sign hε hB hG hG' k l]
    rfl
  have kap : ∀ (α β : ℂ) (k l : Fin W.rank × Fin V.rank),
      GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.commScalar V W τ τ (α • unitMap B B' k.1 k.2) (β • unitMap B B' l.1 l.2) =
        -(2 * Real.pi * Complex.I) * (((2 * (tauE D τ D.host.xi0 * (α * ((starRingEnd ℂ) β *
          (if k = l then ((ε' k.1 * ε k.2 : ℝ) : ℂ) else 0)))).re : ℝ)) : ℂ) := by
    intro α β k l
    unfold GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.commScalar GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.hermAt
    rw [if_pos rfl, htr]
  have kap0 : ∀ (α β : ℂ) (k l : Fin W.rank × Fin V.rank), k ≠ l →
      GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.commScalar V W τ τ (α • unitMap B B' k.1 k.2) (β • unitMap B B' l.1 l.2) = 0 := by
    intro α β k l hkl
    rw [kap, if_neg hkl]
    simp
  have kapI : ∀ k : Fin W.rank × Fin V.rank,
      GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.commScalar V W τ τ (unitMap B B' k.1 k.2) ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) =
        -(4 * Real.pi * Complex.I) * ((tauE D τ D.host.xi0).im : ℂ) := by
    intro k
    have e := kap 1 (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) k k
    rw [one_smul] at e
    rw [e, if_pos rfl]
    have h2 : (tauE D τ D.host.xi0 * (1 * ((starRingEnd ℂ) (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) * ((ε' k.1 * ε k.2 : ℝ) : ℂ)))).re =
        (tauE D τ D.host.xi0).im := by
      have e2 : (1 : ℂ) * ((starRingEnd ℂ) (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) =
          -Complex.I * (((ε' k.1 * ε k.2) * (ε' k.1 * ε k.2) : ℝ) : ℂ) := by
        rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
        push_cast
        ring
      rw [e2, hσ k]
      simp [Complex.mul_re]
    rw [h2]
    push_cast
    ring
  have hA : ∀ (k : Fin W.rank × Fin V.rank) h, Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) h = (fockScale D τ : ℂ)⁻¹ • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (unitMap B B' k.1 k.2) h + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) h := by
    intro k h
    unfold Formalism.IndefR.Datum.aPlus Formalism.IndefR.Datum.crea
    rw [hJ k]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hBo : ∀ (k : Fin W.rank × Fin V.rank) h, ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) h) = (-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (unitMap B B' k.1 k.2) h + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) h := by
    intro k h
    unfold Formalism.IndefR.Datum.annih
    rw [hJ k]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have Ath : ∀ (k : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) := by
    intro k g hg
    rw [hA]
    exact GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (Dth _ _ hg)) (GlobalTheory.OrientedHeis.theta_smul _ (Dth _ _ hg))
  have Bth : ∀ (k : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) := by
    intro k g hg
    rw [hBo]
    exact GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (Dth _ _ hg)) (GlobalTheory.OrientedHeis.theta_smul _ (Dth _ _ hg))
  have Aadd : ∀ (k : Fin W.rank × Fin V.rank) g h, IsThetaFunO ψ V W g → IsThetaFunO ψ V W h → Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (g + h) = Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g + Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) h := by
    intro k g h hg hh
    simp only [hA]
    rw [GlobalTheory.Size.dRho_add hψ hθ τ _ hg hh, GlobalTheory.Size.dRho_add hψ hθ τ _ hg hh]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have Badd : ∀ (k : Fin W.rank × Fin V.rank) g h, IsThetaFunO ψ V W g → IsThetaFunO ψ V W h → ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (g + h)) = ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) + ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) h) := by
    intro k g h hg hh
    simp only [hBo]
    rw [GlobalTheory.Size.dRho_add hψ hθ τ _ hg hh, GlobalTheory.Size.dRho_add hψ hθ τ _ hg hh]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have Asmul : ∀ (k : Fin W.rank × Fin V.rank) (c : ℂ) g, Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (c • g) = c • Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g := by
    intro k c g
    simp only [hA]
    rw [GlobalTheory.Size.dRho_smul, GlobalTheory.Size.dRho_smul]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have Bsmul : ∀ (k : Fin W.rank × Fin V.rank) (c : ℂ) g, ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (c • g)) = c • ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) := by
    intro k c g
    simp only [hBo]
    rw [GlobalTheory.Size.dRho_smul, GlobalTheory.Size.dRho_smul]
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have ccr1 : ∀ (k l : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g → Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' l.1 l.2) g) = Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' l.1 l.2) (Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) := by
    intro k l g hg
    by_cases hkl : k = l
    · rw [hkl]
    · have L := fun z z1 z2 (α β : ℂ) => Dlin z α β (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z1 g) (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z2 g) (Dth z1 g hg) (Dth z2 g hg)
      simp only [hA, L]
      funext x
      have k1 := kap0 1 1 k l hkl
      rw [one_smul, one_smul] at k1
      have k2 := kap0 1 (Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) k l hkl
      rw [one_smul] at k2
      have k3 := kap0 (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) 1 k l hkl
      rw [one_smul] at k3
      have k4 := kap0 (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) (Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) k l hkl
      have e1 := Cm (unitMap B B' k.1 k.2) (unitMap B B' l.1 l.2) g hg x
      have e2 := Cm (unitMap B B' k.1 k.2) ((Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) • unitMap B B' l.1 l.2) g hg x
      have e3 := Cm ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) (unitMap B B' l.1 l.2) g hg x
      have e4 := Cm ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) ((Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) • unitMap B B' l.1 l.2) g hg x
      rw [k1] at e1
      rw [k2] at e2
      rw [k3] at e3
      rw [k4] at e4
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ * e1 + (fockScale D τ : ℂ)⁻¹ * (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * e2 + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * (fockScale D τ : ℂ)⁻¹ * e3 + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * e4
  have ccr2 : ∀ (k l : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g →
      ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' l.1 l.2) g)) = Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' l.1 l.2) ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) + (@ite ℂ (k = l) (Classical.propDecidable (k = l)) 1 0) • g := by
    intro k l g hg
    have L := fun z z1 z2 (α β : ℂ) => Dlin z α β (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z1 g) (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z2 g) (Dth z1 g hg) (Dth z2 g hg)
    simp only [hA, hBo, L]
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl]
      funext x
      have e2 := Cm (unitMap B B' k.1 k.2) ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) g hg x
      rw [kapI k] at e2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination ((-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * (-(fockScale D τ : ℂ)⁻¹ - (fockScale D τ : ℂ)⁻¹)) * e2 + (g x) * hcinv +
        (-(8 * Real.pi) * (fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ * ((tauE D τ D.host.xi0).im : ℂ) * g x) * Complex.I_mul_I
    · rw [if_neg hkl]
      funext x
      have k1 := kap0 1 1 k l hkl
      rw [one_smul, one_smul] at k1
      have k2 := kap0 1 (Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) k l hkl
      rw [one_smul] at k2
      have k3 := kap0 (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) 1 k l hkl
      rw [one_smul] at k3
      have k4 := kap0 (Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) (Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) k l hkl
      have e1 := Cm (unitMap B B' k.1 k.2) (unitMap B B' l.1 l.2) g hg x
      have e2 := Cm (unitMap B B' k.1 k.2) ((Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) • unitMap B B' l.1 l.2) g hg x
      have e3 := Cm ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) (unitMap B B' l.1 l.2) g hg x
      have e4 := Cm ((Complex.I * ((ε' k.1 * ε k.2 : ℝ) : ℂ)) • unitMap B B' k.1 k.2) ((Complex.I * ((ε' l.1 * ε l.2 : ℝ) : ℂ)) • unitMap B B' l.1 l.2) g hg x
      rw [k1] at e1
      rw [k2] at e2
      rw [k3] at e3
      rw [k4] at e4
      simp only [ Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(fockScale D τ : ℂ)⁻¹) * (fockScale D τ : ℂ)⁻¹ * e1 + (-(fockScale D τ : ℂ)⁻¹) * (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * e2 + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * (fockScale D τ : ℂ)⁻¹ * e3 + (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * (-((fockScale D τ : ℂ)⁻¹ * Complex.I)) * e4
  have hex : ∀ T : (WO V W → ℂ) → (WO V W → ℂ), (∀ g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (T g)) →
      (∀ g h, IsThetaFunO ψ V W g → IsThetaFunO ψ V W h → T (g + h) = T g + T h) → (∀ (c : ℂ) g, T (c • g) = c • T g) →
      ∃ e : Module.End ℂ (GlobalTheory.VacuumFockLaws.thetaSub V W ψ), ∀ g : GlobalTheory.VacuumFockLaws.thetaSub V W ψ, (e g : WO V W → ℂ) = T g :=
    fun T h1 h2 h3 => exists_end_coe_eq_of_linear_on_submodule _ T (fun g hg => h1 g hg) (fun g hg h hh => h2 g h hg hh) (fun c g _ => h3 c g)
  choose a ha using fun k : Fin W.rank × Fin V.rank => hex (fun g => Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g) (Ath k) (Aadd k) (Asmul k)
  choose b hb using fun k : Fin W.rank × Fin V.rank => hex (fun g => ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) g)) (Bth k) (Badd k) (Bsmul k)
  have ha' : ∀ (k : Fin W.rank × Fin V.rank) (g : GlobalTheory.VacuumFockLaws.thetaSub V W ψ), (a k g : WO V W → ℂ) = Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (g : WO V W → ℂ) := fun k g => ha k g
  have hb' : ∀ (k : Fin W.rank × Fin V.rank) (g : GlobalTheory.VacuumFockLaws.thetaSub V W ψ), (b k g : WO V W → ℂ) = ((-(fockScale D τ : ℂ)⁻¹) • Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) (g : WO V W → ℂ)) := fun k g => hb k g
  have haa : ∀ i j (g : GlobalTheory.VacuumFockLaws.thetaSub V W ψ), a i (a j g) = a j (a i g) := by
    intro i j g
    apply Subtype.ext
    simp only [ha']
    exact ccr1 i j g g.2
  have hba : ∀ i j (g : GlobalTheory.VacuumFockLaws.thetaSub V W ψ), b i (a j g) = a j (b i g) + (@ite ℂ (i = j) (Classical.propDecidable (i = j)) 1 0) • g := by
    intro i j g
    apply Subtype.ext
    simp only [ha', hb', Submodule.coe_add, Submodule.coe_smul]
    exact ccr2 i j g g.2
  have hv : ∀ z, Formalism.IndefR.Datum.annih (heisO ψ V W) θ τ (cplxO s s') z f = 0 := hvac
  have hfb : ∀ i, b i ⟨f, hf⟩ = 0 := by
    intro i
    apply Subtype.ext
    rw [hb']
    simp [hv]
  have R := GlobalTheory.VacuumFockLaws.fock_of_ccr (ι := Fin W.rank × Fin V.rank) (X := WO V W) (GlobalTheory.VacuumFockLaws.thetaSub V W ψ) (fun (k : Fin W.rank × Fin V.rank) (h : WO V W → ℂ) => Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO s s') (unitMap B B' k.1 k.2) h) a b
    (fun k g => (ha' k g).symm) haa hba ⟨f, hf⟩ hfb
  have thP : ∀ P, IsThetaFunO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) := fun P => R.1 P
  have IPkey : ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL W V) 𝓕 μ → ∀ (β : Fin W.rank × Fin V.rank →₀ ℕ)
        (Q : MvPolynomial (Fin W.rank × Fin V.rank) ℂ),
        ipO μ 𝓕 (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f Q) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f (MvPolynomial.monomial β 1)) = Q.coeff β * ((multiFact β : ℂ) * ipO μ 𝓕 f f) := by
    intro μ 𝓕 hμ h𝓕
    have ipL : ∀ (α β : ℂ) F G H, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → IsThetaFunO ψ V W H →
        ipO μ 𝓕 (α • F + β • G) H = α * ipO μ 𝓕 F H + β * ipO μ 𝓕 G H := by
      intro α β F G H hF hG hH
      rw [GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul α hF) (GlobalTheory.OrientedHeis.theta_smul β hG) hH,
        GlobalTheory.Size.ipO_smul_left, GlobalTheory.Size.ipO_smul_left]
    have ipR : ∀ (α β : ℂ) F G H, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → IsThetaFunO ψ V W H →
        ipO μ 𝓕 H (α • F + β • G) = (starRingEnd ℂ) α * ipO μ 𝓕 H F + (starRingEnd ℂ) β * ipO μ 𝓕 H G := by
      intro α β F G H hF hG hH
      rw [GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 hH (GlobalTheory.OrientedHeis.theta_smul α hF) (GlobalTheory.OrientedHeis.theta_smul β hG),
        GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_right]
    have sk : ∀ z F H, IsThetaFunO ψ V W F → IsThetaFunO ψ V W H → ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z F) H = -ipO μ 𝓕 F (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z H) :=
      fun z F H hF hH => (hsk τ z).2.2 μ 𝓕 hμ h𝓕 F H hF hH
    apply R.2 (ipO μ 𝓕)
    · intro x y z
      exact GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 x.2 y.2 z.2
    · intro c x z
      exact GlobalTheory.Size.ipO_smul_left (μ := μ) (𝓕 := 𝓕) c x z
    · intro x
      have e := GlobalTheory.Size.ipO_smul_right (μ := μ) (𝓕 := 𝓕) (0 : ℂ) x 0
      simpa using e
    · intro i x y
      have hx : IsThetaFunO ψ V W (x : WO V W → ℂ) := x.2
      have hy : IsThetaFunO ψ V W (y : WO V W → ℂ) := y.2
      simp only [ha', hb', hA, hBo]
      rw [ipL _ _ _ _ _ (Dth _ _ hx) (Dth _ _ hx) hy, ipR _ _ _ _ _ (Dth _ _ hy) (Dth _ _ hy) hx,
        sk _ _ _ hx hy, sk _ _ _ hx hy, map_neg, hconj, hconjE]
      ring
    · intro i x y
      have hx : IsThetaFunO ψ V W (x : WO V W → ℂ) := x.2
      have hy : IsThetaFunO ψ V W (y : WO V W → ℂ) := y.2
      simp only [ha', hb', hA, hBo]
      rw [ipR _ _ _ _ _ (Dth _ _ hy) (Dth _ _ hy) hx, ipL _ _ _ _ _ (Dth _ _ hx) (Dth _ _ hx) hy,
        sk _ _ _ hx hy, sk _ _ _ hx hy, hconj, hconjE]
      ring
  refine ⟨thP, fun hne => ?_, fun μ 𝓕 hμ h𝓕 P Q => ?_⟩
  · intro P Q hPQ
    obtain ⟨μ, 𝓕, hcov⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) V W
    obtain ⟨hμ, h𝓕, -⟩ := hcov
    have key := IPkey μ 𝓕 hμ h𝓕
    have hff : ipO μ 𝓕 f f ≠ 0 := fun h0 => hne ((GlobalTheory.Size.ipO_self_eq_zero_iff hψ hμ h𝓕 hf).mp h0)
    ext β
    have e1 := key β P
    have e2 := key β Q
    rw [hPQ] at e1
    have hm : (multiFact β : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      unfold multiFact
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.mpr fun a _ => Nat.factorial_ne_zero _
    exact mul_right_cancel₀ (mul_ne_zero hm hff) (e1.symm.trans e2)
  · have key := IPkey μ 𝓕 hμ h𝓕
    have lin : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f Q = ∑ β ∈ Q.support, Q.coeff β • GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f (MvPolynomial.monomial β 1) := by
      conv_lhs => rw [Q.as_sum]
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt Formalism.IndefR.Datum.pureTensorL
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro β _
      rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have thsum : ∀ (t : Finset (Fin W.rank × Fin V.rank →₀ ℕ)) (cf : (Fin W.rank × Fin V.rank →₀ ℕ) → ℂ),
        IsThetaFunO ψ V W (∑ β ∈ t, cf β • GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f (MvPolynomial.monomial β 1)) := by
      intro t cf
      refine Finset.induction_on t ?_ ?_
      · rw [Finset.sum_empty]
        exact GlobalTheory.OrientedHeis.theta_zero
      · intro β t hβ ih
        rw [Finset.sum_insert hβ]
        exact GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (thP _)) ih
    have ipRs : ∀ (t : Finset (Fin W.rank × Fin V.rank →₀ ℕ)) (cf : (Fin W.rank × Fin V.rank →₀ ℕ) → ℂ),
        ipO μ 𝓕 (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) (∑ β ∈ t, cf β • GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f (MvPolynomial.monomial β 1)) =
          ∑ β ∈ t, (starRingEnd ℂ) (cf β) * ipO μ 𝓕 (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f (MvPolynomial.monomial β 1)) := by
      intro t cf
      refine Finset.induction_on t ?_ ?_
      · rw [Finset.sum_empty, Finset.sum_empty]
        have e := GlobalTheory.Size.ipO_smul_right (μ := μ) (𝓕 := 𝓕) (0 : ℂ) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) 0
        simpa using e
      · intro β t hβ ih
        rw [Finset.sum_insert hβ, Finset.sum_insert hβ,
          GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (thP P) (GlobalTheory.OrientedHeis.theta_smul _ (thP _)) (thsum t cf),
          GlobalTheory.Size.ipO_smul_right, ih]
    rw [lin, ipRs, fockIp_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    rw [key β P]
    ring

variable {D : D7} {V W : HSp D}

theorem laws {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) {s B : Mn V.rank} {s' B' : Mn W.rank} {ε : Fin V.rank → ℝ} {ε' : Fin W.rank → ℝ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) (hε' : ∀ a, ε' a = 1 ∨ ε' a = -1) (hB : IsUnit B.det)
    (hs : s * B = B * diagonal fun a => (ε a : ℂ)) (hs' : s' * B' = B' * diagonal fun a => (ε' a : ℂ))
    (hG : Bᴴ * gramAt D V τ * B = diagonal fun a => (ε a : ℂ))
    (hG' : B'ᴴ * gramAt D W τ * B' = diagonal fun a => (ε' a : ℂ)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hvac : IsFockVacAt (heisO ψ V W) θ τ (cplxO s s') f) :
    (∀ P, IsThetaFunO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P)) ∧
      (f ≠ 0 → Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f)) ∧
      ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ →
        ∀ P Q, ipO μ 𝓕 (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f P) (GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W τ s s' B B' f Q) =
          ipO μ 𝓕 f f * fockIp P Q :=
  laws_lemma_7 hψ hθ τ hε hε' hB hs hs' hG hG' hf hvac

end Laws

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem fock_at_one_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → (∀ P, IsThetaFunO ψ S T (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P)) ∧ (f ≠ 0 → Function.Injective (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ N, Fischer (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) (ipTh μ 𝓕) (LinearEquiv.refl ℂ _) N) := by
  intro D ψ θ S T τ hψ hθ sS frS εS sT frT εT hS hT f hf hvac
  obtain ⟨hdS, hsS, hGS⟩ := frame_inv hS
  obtain ⟨hdT, hsT, hGT⟩ := frame_inv hT
  have L := laws (D := D) (V := S) (W := T) hψ hθ τ (ε := fun a => sgn εS a) (ε' := fun a => sgn εT a)
    (fun a => sgn_cases εS a) (fun a => sgn_cases εT a) hdS hsS hsT hGS hGT hf hvac
  refine ⟨L.1, fun hne => ⟨L.2.1 hne, ?_⟩⟩
  intro μ 𝓕 hμ h𝓕
  have hne0 : GlobalTheory.Ker.ipO μ 𝓕 f f ≠ 0 := fun h0 =>
    hne ((GlobalTheory.Size.ipO_self_eq_zero_iff hψ hμ h𝓕 hf).mp h0)
  have hre : GlobalTheory.Ker.ipO μ 𝓕 f f = (((GlobalTheory.Ker.ipO μ 𝓕 f f).re : ℝ) : ℂ) := by
    have hc : (starRingEnd ℂ) (GlobalTheory.Ker.ipO μ 𝓕 f f) = GlobalTheory.Ker.ipO μ 𝓕 f f :=
      GlobalTheory.Size.ipO_conj (μ := μ) (𝓕 := 𝓕) f f
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · have him := congrArg Complex.im hc
      rw [Complex.conj_im] at him
      simp only [Complex.ofReal_im]
      linarith
  have hnn : 0 ≤ (GlobalTheory.Ker.ipO μ 𝓕 f f).re := by
    have hI := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 hf hf
    unfold GlobalTheory.Ker.ipO
    have key : (∫ w in 𝓕, f w * (starRingEnd ℂ) (f w) ∂μ).re =
        ∫ w in 𝓕, (f w * (starRingEnd ℂ) (f w)).re ∂μ := (integral_re hI).symm
    rw [key]
    exact MeasureTheory.integral_nonneg fun w => by
      simp only [Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_nonneg _
  have hpos : 0 < (GlobalTheory.Ker.ipO μ 𝓕 f f).re := by
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [hre, ← h, Complex.ofReal_zero]) hne0
  refine ⟨(GlobalTheory.Ker.ipO μ 𝓕 f f).re, ?_⟩
  unfold GlobalTheory.ArchRec.Fischer
  refine ⟨hpos, fun P Q => ?_⟩
  rw [LinearEquiv.refl_apply, LinearEquiv.refl_apply, ← hre, ← L.2.2 μ 𝓕 hμ h𝓕 P Q]
  rfl

end Main

end GlobalTheory.OnePlaceFock

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_at_one_realPlace_over_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → (∀ P, IsThetaFunO ψ S T (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P)) ∧ (f ≠ 0 → Function.Injective (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ N, Fischer (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) (ipTh μ 𝓕) (LinearEquiv.refl ℂ _) N) := by
  first | exact @GlobalTheory.OnePlaceFock.fock_at_one_place | exact GlobalTheory.OnePlaceFock.fock_at_one_place | (intros; apply GlobalTheory.OnePlaceFock.fock_at_one_place <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockPolynomial_operator_heisenberg_derivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, ∃ L : Module.End ℂ (LPol T.rank S.rank), ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → ∀ P, dRho (heisO ψ S T) θ τ z (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P) = ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f (L P) := by
  first | exact @GlobalTheory.ArchRec.DerFock.exists_dRho_ptAt | exact GlobalTheory.ArchRec.DerFock.exists_dRho_ptAt | (intros; apply GlobalTheory.ArchRec.DerFock.exists_dRho_ptAt <;> assumption)
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped Classical

namespace GlobalTheory.ArchRec.Gen

theorem xOp_dOp {ι : Type} [Fintype ι] [DecidableEq ι] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (ρ : (ι → ℂ) → B →L[ℂ] B) (H : Matrix ι ι ℂ) (k l : ι) {f : B} (hd : ∀ v, GlobalTheory.RealWeil.Sm ρ (dH ρ v f)) :
    xOp ρ k (dOp ρ H l f) = ∑ b : Bool × Bool,
      (-(1 / (4 * Real.pi)) * (if b.1 then -Complex.I else 1) * (if b.2 then Complex.I else 1) : ℂ) •
        dH ρ ((if b.1 then Complex.I else 1) • Pi.single k 1)
          (dH ρ ((if b.2 then Complex.I else 1) • H⁻¹ *ᵥ Pi.single l 1) f) := by
  have hs : ∀ (a : ℂ) v, GlobalTheory.RealWeil.Sm ρ (a • dH ρ v f) := fun a v => (smS ρ).smul_mem a (hd v)
  have ha : ∀ (a : ℂ) u v, GlobalTheory.RealWeil.Sm ρ (dH ρ u f + a • dH ρ v f) := fun a u v => (smS ρ).add_mem (hd u) (hs a v)
  simp only [xOp, dOp, dH_smul _ _ (ha _ _ _), dH_add _ (hd _) (hs _ _), dH_smul _ _ (hd _), Fintype.sum_prod_type,
    Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, one_smul]
  module

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ}
  {S T : HSp D}

theorem coe_dH_at (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : IsThetaFunO ψ S T F.1) (τ : D.what₂.Tau) (v : GlobalTheory.RealWeil.Ix S T → ℂ) (hv : ∀ k, k.2 ≠ τ → v k = 0) :
    ((dH (rhoV hψ σ S T) v F).1 : WO S T → ℂ) = Datum.dRho (heisO ψ S T) θ τ (cpt v τ) F.1 := by
  have e : v = vecL (Pi.single τ (cpt v τ) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
    funext ⟨⟨a, a'⟩, t⟩
    change _ = (Pi.single τ (cpt v τ) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) t a a'
    by_cases ht : t = τ
    · subst ht
      rw [Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne ht]
      exact hv _ ht
  rw [← GlobalTheory.DefLift.Gen.coe_dH h hψ F hF, ← e]

open scoped ComplexOrder in

theorem HM_inv_apply (k l : GlobalTheory.RealWeil.Ix S T) (hkl : k.2 ≠ l.2) : (HM S T)⁻¹ k l = 0 := by
  have : HM S T * blk (fun τ => ((2 * (tauE D τ D.host.xi0).im : ℝ) : ℂ)⁻¹ • (gramAt D T τ)⁻¹) (gramAt D S) = 1 := by
    unfold HM
    rw [blk_mul, ← blk_one]
    congr 1 <;> funext τ
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (two_im_pos τ).ne', one_smul,
        mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit T τ)]
    · rw [mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ)]
  rw [inv_eq_right_inv this, WeylAction.blk_apply, if_neg hkl]

theorem nOp_at (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (hX : ∀ k l, k.2 ≠ τ ∨ l.2 ≠ τ → X k l = 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (z z' : Fin n → Matrix (Fin T.rank) (Fin S.rank) ℂ), ∀ F : BB ψ S T,
      IsThetaFunO ψ S T F.1 → ((nOp (rhoV hψ σ S T) (HM S T) X F).1 : WO S T → ℂ) =
        ∑ i, c i • Datum.dRho (heisO ψ S T) θ τ (z i) (Datum.dRho (heisO ψ S T) θ τ (z' i) F.1) := by
  let e := (Fintype.equivFin (GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool)).symm
  let c : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → ℂ := fun a => X a.1 a.2.1 *
    (-(1 / (4 * Real.pi)) * (if a.2.2.1 then -Complex.I else 1) * (if a.2.2.2 then Complex.I else 1))
  let u : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → GlobalTheory.RealWeil.Ix S T → ℂ := fun a =>
    (if a.2.2.1 then Complex.I else 1) • Pi.single a.1 1
  let u' : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → GlobalTheory.RealWeil.Ix S T → ℂ := fun a =>
    (if a.2.2.2 then Complex.I else 1) • (HM S T)⁻¹ *ᵥ Pi.single a.2.1 1
  refine ⟨_, c ∘ e, fun i => cpt (u (e i)) τ, fun i => cpt (u' (e i)) τ, fun F hF => ?_⟩
  have th := GlobalTheory.DefLift.Gen.theta_dH h hψ F hF
  have e1 : nOp (rhoV hψ σ S T) (HM S T) X F =
      ∑ a, c a • dH (rhoV hψ σ S T) (u a) (dH (rhoV hψ σ S T) (u' a) F) := by
    rw [nOp, Fintype.sum_prod_type (f := fun a => c a • dH (rhoV hψ σ S T) (u a) (dH (rhoV hψ σ S T) (u' a) F))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_prod_type (f := fun a => c (k, a) • dH (rhoV hψ σ S T) (u (k, a))
      (dH (rhoV hψ σ S T) (u' (k, a)) F))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [xOp_dOp _ _ _ _ fun v => sm_of_theta h hψ _ (th v), Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => smul_smul _ _ _
  let j : BB ψ S T →ₗ[ℂ] (WO S T → ℂ) := ⟨⟨fun G => G.1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  change j _ = _
  rw [e1, map_sum, ← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Function.comp_apply]
  beta_reduce
  generalize e i = a
  by_cases ha : a.1.2 ≠ τ ∨ a.2.1.2 ≠ τ
  · have : c a = 0 := by simp only [c, hX _ _ ha, zero_mul]
    rw [this, zero_smul, zero_smul]
  · push Not at ha
    have h1 : ∀ k, k.2 ≠ τ → u a k = 0 := fun k hk => by
      have : k ≠ a.1 := fun e => hk (e ▸ ha.1)
      simp only [u, Pi.smul_apply, Pi.single_eq_of_ne this, smul_zero]
    have h2 : ∀ k, k.2 ≠ τ → u' a k = 0 := fun k hk => by
      simp only [u', Pi.smul_apply, mulVec_single_one, col_apply, HM_inv_apply k a.2.1 (ha.2 ▸ hk), smul_zero]
    rw [← coe_dH_at h hψ F hF τ _ h2, ← coe_dH_at h hψ _ (th _) τ _ h1]
    rfl

variable {χS χT : (AE D)ˣ →* Circle} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem quadGen_of_supp (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT ω) (τ : D.what₂.Tau)
    (γ : ℝ → GA D S × GA D T) (h1 : Continuous γ) (h2 : ∀ s t, γ (s + t) = γ s * γ t)
    (h3 : ∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ)
    (h4 : ∀ k l, HasDerivAt (fun t => mM θ S T (γ t) k l) (X k l) 0) (hX : ∀ k l, k.2 ≠ τ ∨ l.2 ≠ τ → X k l = 0) :
    QuadGen ψ θ τ ω γ := by
  have hψ := hω.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  obtain ⟨lam, hl⟩ := GenZero.exists_generator D θ σ h ψ hψ S T ω hW hω.om_cont γ h1 h2 h3 X h4
  obtain ⟨lam', hl'⟩ := GlobalTheory.Mem.LiftGen.hasDerivAt_om D θ σ h ψ hψ S T ω hW hω.om_cont γ h1 h2 h3 X h4
  obtain ⟨n, c, z, z', hq⟩ := nOp_at h hψ τ X hX
  refine ⟨n, c, z, z', lam, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f := ⟨toB hψ f hf, coe_toB hψ f hf⟩
  obtain ⟨u, hu, hud⟩ := hl F hf
  rw [← hq F hf, GlobalTheory.DefLift.Gen.coe_add_smul]
  have hl2 := hl' F hf
  generalize nOp (rhoV hψ σ S T) (HM S T) X F + lam • F = G at hud ⊢
  generalize nOp (rhoV hψ σ S T) (HM S T) X F + lam' • F = G' at hl2
  have e : (G.1 : WO S T → ℂ) = G'.1 := funext fun w => by
    have a1 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hud
    have a2 := hl2 1 w
    simp only [one_mul, map_one, Module.End.one_apply] at a2
    refine HasDerivAt.unique ?_ a2
    exact a1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun (hu t) w).symm)
  refine ⟨fun g w => by rw [e]; exact hl2 g w, fun μ 𝓕 hμ h𝓕 E hE => ?_⟩
  obtain ⟨E, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = E := ⟨toB hψ E hE, coe_toB hψ E hE⟩
  obtain ⟨i1, i2, i3, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (GlobalTheory.Size.measure_dom hμ h𝓕).2
  let Φ : BB ψ S T →L[ℂ] ℂ := (innerSL ℂ (toL2 _ _ (μ.restrict 𝓕) E)).comp (toL2 _ _ (μ.restrict 𝓕))
  have hΦ : ∀ A : BB ψ S T, ipTh μ 𝓕 A.1 E.1 = Φ A := fun A =>
    (BoundedContinuousFunction.inner_toLp (μ.restrict 𝓕) E.1 A.1).symm
  simp only [← hu, hΦ]
  exact (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hud

theorem quadGen_oneP : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → (∀ X ∈ lieAt S τ, QuadGen ψ θ τ ω fun t => (oneP θ S τ X t, 1)) ∧ ∀ Y ∈ lieAt T τ, QuadGen ψ θ τ ω fun t => (1, oneP θ T τ Y t) := by
  intro D ψ θ S T χS χT ω τ hθ hω
  have supp : ∀ (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
      (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ t, t ≠ τ → b t = 0 ∨ a t = 0) →
      ∀ k l : GlobalTheory.RealWeil.Ix S T, k.2 ≠ τ ∨ l.2 ≠ τ → blk b a k l = 0 := by
    intro b a hab k l hkl
    rw [WeylAction.blk_apply]
    split_ifs with e
    · rcases hab k.2 (hkl.elim id fun h => e ▸ h) with h | h <;> simp [h]
    · rfl
  refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
  · refine quadGen_of_supp hθ hω τ _ ((continuous_oneP hθ hX).prodMk continuous_const)
      (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨(isAtTau_oneP hθ hX t).1, one_mem _⟩) (blk (fun _ => 1) (Pi.single τ (-X))) (fun k l => ?_)
      (supp _ _ fun t ht => Or.inr (Pi.single_eq_of_ne ht _))
    simp only [mM_apply, WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one,
      WeylAction.blk_apply]
    split_ifs
    · exact (WeylAction.hasDerivAt_comp hθ (WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _
    · exact hasDerivAt_const _ _
  · refine quadGen_of_supp hθ hω τ _ (continuous_const.prodMk (continuous_oneP hθ hY))
      (fun s t => by rw [oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨one_mem _, (isAtTau_oneP hθ hY t).1⟩) (blk (Pi.single τ Y) fun _ => 1) (fun k l => ?_)
      (supp _ _ fun t ht => Or.inl (Pi.single_eq_of_ne ht _))
    simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, WeylAction.blk_apply]
    split_ifs
    · exact (WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _
    · exact hasDerivAt_const _ _

end GlobalTheory.ArchRec.Gen

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilGenerator_quadratic_oneParameter_at_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → (∀ X ∈ lieAt S τ, QuadGen ψ θ τ ω fun t => (oneP θ S τ X t, 1)) ∧ ∀ Y ∈ lieAt T τ, QuadGen ψ θ τ ω fun t => (1, oneP θ T τ Y t) := by
  atlas_forward_decl GlobalTheory.ArchRec.Gen.quadGen_oneP
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
open GlobalTheory.ChainFr (Fr ptF IsVacF)

noncomputable section

namespace GlobalTheory.ArchRec.LieAtPlace

variable {D : D7}

open scoped ComplexOrder in

theorem cart_isCartanInv {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (A.cart τ) := by
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))
  have h2 : (A.fr τ)⁻¹ * A.fr τ = 1 := mul_eq_one_comm.1 h1
  have hJ := Formalism.REAL.Jm_mul_self (A.ε τ)
  have hJ' := Formalism.REAL.Jm_conjTranspose (A.ε τ)
  have hG : gramAt D V τ * A.cart τ = (A.fr τ)ᴴ * A.fr τ := by
    rw [← A.fr_gram τ]; unfold Fr.cart
    calc _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : A.cart τ * A.cart τ = 1 := by
    unfold Fr.cart
    calc _ = (A.fr τ)⁻¹ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← A.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (A.fr_unit τ))

theorem exists_fr {V : HSp D} {τ : D.what₂.Tau} {s fr : Mn V.rank} {ε : Fin V.rank → Bool}
    (h : IsFrameOf (gramAt D V τ) s ε fr) : ∃ A : Fr V, A.ε τ = ε ∧ A.fr τ = fr ∧ A.cart τ = s := by
  classical
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V).1
  refine ⟨⟨Function.update A.ε τ ε, Function.update A.fr τ fr, fun ρ => ?_, fun ρ => ?_⟩, by simp, by simp, ?_⟩
  · by_cases e : ρ = τ
    · subst e; rw [Function.update_self]; exact h.1
    · rw [Function.update_of_ne e]; exact A.fr_unit ρ
  · by_cases e : ρ = τ
    · subst e; rw [Function.update_self, Function.update_self]; exact h.2.1
    · rw [Function.update_of_ne e, Function.update_of_ne e]; exact A.fr_gram ρ
  · simp [Fr.cart, h.2.2]

theorem pure_rename {ι κ X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {A' : κ → (X → ℂ) → (X → ℂ)} {g : X → ℂ}
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (e : κ → ι) (h : ∀ k, A (e k) = A' k) (Q : MvPolynomial κ ℂ) :
    pureTensorL A g (MvPolynomial.rename e Q) = pureTensorL A' g Q := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, ← mul_one (MvPolynomial.C a : MvPolynomial ι ℂ),
      ← mul_one (MvPolynomial.C a : MvPolynomial κ ℂ), MvPolynomial.C_mul', MvPolynomial.C_mul', map_smul, map_smul,
      GlobalTheory.FockIndep.pure_one, GlobalTheory.FockIndep.pure_one]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, map_mul (MvPolynomial.rename e), MvPolynomial.rename_X, hX, hX', hp, h]

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem ptF_rename (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr T) (τ : D.what₂.Tau)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : LPol T.rank S.rank) :
    ptF ψ θ A B f (MvPolynomial.rename (fun s => (τ, s)) P) =
      ptAt ψ θ S T τ (A.cart τ) (B.cart τ) (A.fr τ)⁻¹ (B.fr τ)⁻¹ f P := by
  have hS := cart_isCartanInv A
  have hT := cart_isCartanInv B
  refine pure_rename (fun v Q => ?_) (fun v Q => ?_) _ (fun k => rfl) P
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ τ _ hS hT τ _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h

theorem ins_one {a b : ℕ} (τ : D.what₂.Tau) (p : LPol b a) :
    GlobalTheory.Chain.RealIt.GlueProof.ins τ (fun _ => 1) p = (MvPolynomial.rename (fun s => (τ, s)) p : PolF D b a) := by
  rw [GlobalTheory.Chain.RealIt.GlueProof.ins_apply]
  simp [GlobalTheory.Chain.RealIt.GlueProof.rest]

theorem derAll_of_one (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ : D.what₂.Tau}
    {sS frS : Mn S.rank} {εS : Fin S.rank → Bool} {sT frT : Mn T.rank} {εT : Fin T.rank → Bool}
    (hS : IsFrameOf (gramAt D S τ) sS εS frS) (hT : IsFrameOf (gramAt D T τ) sT εT frT)
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {γ : ℝ → GA D S × GA D T} (hγ : QuadGen ψ θ τ ω γ)
    {f₀ : WO S T → ℂ} (h0 : IsThetaFunO ψ S T f₀) (v0 : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f₀) (n0 : f₀ ≠ 0)
    {P P' : LPol T.rank S.rank}
    (hd : ∀ z, HasDerivAt (fun t : ℝ => ω (γ t) (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f₀ P) z)
      (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f₀ P' z) 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f) :
    DerAll ψ ω γ (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P) (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P') := by
  obtain ⟨k, c, z, z', lam, hq⟩ := hγ
  choose L hL using GlobalTheory.T.exists_fockPolynomial_operator_heisenberg_derivative D ψ θ S T τ hψ hθ sS frS εS sT frT εT hS hT
  have hc := GlobalTheory.T.fockVectors_at_one_realPlace_over_vacuum D ψ θ S T τ hψ hθ sS frS εS sT frT εT hS hT
  have key : ∀ g, IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g →
      DerAll ψ ω γ (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g P)
        (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g ((∑ i, c i • L (z i) (L (z' i) P)) + lam • P)) := fun g hg vg => by
    have h := hq _ ((hc g hg vg).1 P)
    simp only [hL _ g hg vg] at h
    have e : ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g ((∑ i, c i • L (z i) (L (z' i) P)) + lam • P) =
        (∑ i, c i • ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g (L (z i) (L (z' i) P))) +
          lam • ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g P := by
      simp only [ptAt, map_add, map_sum, map_smul]
    rw [e]
    exact h
  have e : P' = (∑ i, c i • L (z i) (L (z' i) P)) + lam • P := by
    refine ((hc f₀ h0 v0).2 n0).1 (funext fun w => (hd w).unique ?_)
    simpa using (key f₀ h0 v0).1 1 w
  rw [e]
  exact key f hf hv

theorem lieAt_of_vacAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ aS aT : ℚ, HasInfExp D χS τ aS → HasInfExp D χT τ aT → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → LieAt ψ θ τ ω εS frS εT frT aS aT (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) := by
  intro D ψ θ S T χS χT ω τ hθ hW aS aT haS haT sS frS εS sT frT εT hS hT f hf hv
  have hψ := hW.std
  obtain ⟨A, rfl, rfl, rfl⟩ := exists_fr hS
  obtain ⟨B, rfl, rfl, rfl⟩ := exists_fr hT
  obtain ⟨f₀, h0, n0⟩ := GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua.exists_isVac_ne_zero hψ hθ (cart_isCartanInv A) (cart_isCartanInv B)
  have hl := GlobalTheory.T.lieAction_fockOperators_scalars_trace D S T A B θ ψ χS χT ω f₀ τ aS aT hθ hW haS haT h0
  have hg := GlobalTheory.T.weilGenerator_quadratic_oneParameter_at_place D ψ θ S T χS χT ω τ hθ hW
  refine ⟨fun X hX P => ?_, fun Y hY P => ?_⟩
  · refine derAll_of_one hψ hθ hS hT (hg.1 X hX) h0.1 (h0.2 τ) n0 (fun z => ?_) hf hv
    have h := hl.1 X hX (MvPolynomial.rename (fun s => (τ, s)) P) z
    rw [← ins_one, GlobalTheory.Chain.RealIt.GlueProof.fockS_ins, ← map_smul, ← map_add, ins_one, ins_one,
      ptF_rename hψ hθ A B τ h0.1, ptF_rename hψ hθ A B τ h0.1, neg_smul, ← sub_eq_add_neg] at h
    exact h
  · refine derAll_of_one hψ hθ hS hT (hg.2 Y hY) h0.1 (h0.2 τ) n0 (fun z => ?_) hf hv
    have h := hl.2 Y hY (MvPolynomial.rename (fun s => (τ, s)) P) z
    rw [← ins_one, GlobalTheory.Chain.RealIt.GlueProof.fockT_ins, ← map_smul, ← map_add, ins_one, ins_one,
      ptF_rename hψ hθ A B τ h0.1, ptF_rename hψ hθ A B τ h0.1] at h
    exact h

end GlobalTheory.ArchRec.LieAtPlace

end
end
