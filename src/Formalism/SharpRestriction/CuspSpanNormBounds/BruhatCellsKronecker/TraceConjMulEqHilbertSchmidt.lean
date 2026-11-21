import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.FlagUnipotentLattices.HalfDeltaL1Bound
import Formalism.FlagUnipotentLattices.KappaAssemblyOf

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

section SlopeTestRemainingChoices

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_highest_weight_unit (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : IsDS ε lam σ) : ∃ w : H, IsHighestUnit ε lam σ w := by
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hσ
  obtain ⟨v, hvS, hv0, hwt⟩ := hS.2.2.2.1
  refine ⟨((‖v‖ : ℂ)⁻¹) • v, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  · exact (le_sSup (show S ∈ {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S} from hS) :
      S ≤ lowKSub ε lam σ) (S.smul_mem _ hvS)
  · intro θ hθ
    rw [map_smul, hwt θ hθ, smul_comm]

theorem hermitian_of_mem_p (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Formalism.REAL.inP ε X) :
    X.IsHermitian ∧ ∀ a b, ε a = ε b → X a b = 0 := by
  obtain ⟨hG, hA⟩ := hX
  unfold Formalism.REAL.inG at hG
  have hs : ∀ c : Fin n, (if ε c = true then (1:ℂ) else -1) ≠ 0 := by
    intro c
    split_ifs <;> norm_num
  constructor
  · show X.conjTranspose = X
    ext a b
    have h1 := congrFun (congrFun hG a) b
    have h2 := congrFun (congrFun hA a) b
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply,
      Matrix.neg_apply, Matrix.zero_apply] at h1 h2
    have h3 : (X.conjTranspose a b - X a b) * (if ε b = true then (1:ℂ) else -1) = 0 := by
      linear_combination h1 - h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right (hs b))
  · intro a b hab
    have h2 := congrFun (congrFun hA a) b
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply] at h2
    rw [hab] at h2
    have h3 : X a b * (2 * (if ε b = true then (1:ℂ) else -1)) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h (mul_ne_zero two_ne_zero (hs b))

end SlopeTestRemainingChoices



section Dec

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]



theorem orth_proj_fix {E : H →L[ℂ] H} {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) {x : H} (hx : x ∈ S) :
    E x = x := by
  obtain ⟨hidem, -, hr⟩ := hE
  rw [← hr] at hx
  obtain ⟨z, rfl⟩ := hx
  have h := congrArg (fun F : H →L[ℂ] H => F z) hidem
  simpa using h



def oneBasedParam (lam : Fin n → ℝ) (i : ℕ) : ℝ := if h : i - 1 < n then lam ⟨i - 1, h⟩ else 0


end Dec

section Core

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def d30f (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (X : Matrix (Fin n) (Fin n) ℂ) (kk : Formalism.REAL.KG ε) : H →L[ℂ] H :=
  ((wtF lam X (Formalism.REAL.toMK kk) : ℝ) : ℂ) • rank1 (σ (Formalism.REAL.toMK kk) w)



end Core

section Core2

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]




end Core2





section Poly

variable {n : ℕ}

theorem hilbert_schmidt_polar_bound (k X : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hX : X.IsHermitian) :
    Formalism.REAL.hs (k * NormedSpace.exp X) ≤ (n : ℝ) * Real.exp (Real.sqrt (Formalism.REAL.hs X)) ^ 2 := by
  have h1 := (Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.polarInv n k X hk hX).2.2.2
  have h2 := h1.trace_nonneg
  have h3 : ∀ g : Matrix (Fin n) (Fin n) ℂ, (g.conjTranspose * g).trace = ((Formalism.REAL.hs g : ℝ) : ℂ) := by
    intro g
    unfold Formalism.REAL.hs Matrix.trace
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm]
    push_cast
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    exact Complex.conj_mul' _
  rw [Matrix.trace_sub, h3, Matrix.trace_smul, Matrix.trace_one] at h2
  have e : Formalism.NuclearRankWeightBounds.D.hs X = Real.sqrt (Formalism.REAL.hs X) := rfl
  rw [e] at h2
  have h5 : (Real.exp (Real.sqrt (Formalism.REAL.hs X)) ^ 2 : ℝ) • ((Fintype.card (Fin n) : ℕ) : ℂ) -
      ((Formalism.REAL.hs (k * NormedSpace.exp X) : ℝ) : ℂ) =
      (((n : ℝ) * Real.exp (Real.sqrt (Formalism.REAL.hs X)) ^ 2 - Formalism.REAL.hs (k * NormedSpace.exp X) : ℝ) : ℂ) := by
    rw [Complex.real_smul, Fintype.card_fin]
    push_cast
    ring
  rw [h5] at h2
  have h6 := Complex.zero_le_real.1 h2
  linarith

end Poly

theorem poly_decay_of_decay_statement (D : Formalism.BasicNotions.D7) (h1 : DiscreteSeriesDecayBound D) :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h → 1 ≤ min (pOf ε) (qOf ε) →
      ∀ w : H, IsLowUnit ε lam σ w → ∀ g ∈ UJset ε,
        ‖⟪w, σ g w⟫_ℂ‖ ≤
          Real.sqrt n ^ (h / (8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ)))) *
            Real.exp (h / (8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))) /
              Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))) *
            Real.sqrt (Formalism.REAL.hs g) ^ (-(h / (8 * Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ))))) := by
  intro n ε lam hlam H _ _ _ σ hσ E hE h hgap hth hq w hw g hg
  obtain ⟨k, X, hk, hX, rfl⟩ := (Formalism.REAL.polar_decomposition_holds n ε).1 g hg
  have hh : 0 ≤ h := le_trans (by positivity) hth
  set q0 : ℝ := ((min (pOf ε) (qOf ε) : ℕ) : ℝ) with hq0
  have hq0' : (1 : ℝ) ≤ q0 := by rw [hq0]; exact_mod_cast hq
  set s : ℝ := Real.sqrt (2 * q0) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  set a : ℝ := h / (8 * s) with ha
  have ha0 : 0 ≤ a := by positivity
  set t : ℝ := Real.sqrt (Formalism.REAL.hs X) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hsX : Formalism.REAL.hs X = t ^ 2 := by
    rw [ht, Real.sq_sqrt]; unfold Formalism.REAL.hs; positivity

  have c1 := Formalism.HermitianLatticeCounting.Final.S7.coeffLeOp H E (σ (k * NormedSpace.exp X)) w hE.2.1 (orth_proj_fix hE hw.2) hw.1
  have c2 := h1 n ε lam hlam H σ hσ E hE h hgap hth k X hk hX
  have c3 : ‖⟪w, σ (k * NormedSpace.exp X) w⟫_ℂ‖ ≤ decBound (min (pOf ε) (qOf ε)) h X := le_trans c1 c2
  refine le_trans c3 ?_

  have hn : 0 < n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have : pOf ε = 0 := by unfold pOf; simp
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have g1 := hilbert_schmidt_polar_bound k X hk.1 (hermitian_of_mem_p ε X hX).1
  have g2 : Real.sqrt (Formalism.REAL.hs (k * NormedSpace.exp X)) ≤ Real.sqrt n * Real.exp t := by
    rw [← Real.sqrt_sq (Real.exp_pos t).le, ← Real.sqrt_mul hnR.le]
    exact Real.sqrt_le_sqrt g1
  have g3 : 0 < Real.sqrt (Formalism.REAL.hs (k * NormedSpace.exp X)) := by
    apply Real.sqrt_pos.2
    have hnn : 0 ≤ Formalism.REAL.hs (k * NormedSpace.exp X) := by unfold Formalism.REAL.hs; positivity
    rcases hnn.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hz : k * NormedSpace.exp X = 0 := by
        ext i j
        unfold Formalism.REAL.hs at heq
        have e1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by positivity))).1
          heq.symm i (Finset.mem_univ _)
        have e2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).1 e1 j (Finset.mem_univ _)
        simpa using e2
      have hJ : Formalism.REAL.Jm ε = 0 := by
        have : Formalism.REAL.inUJ ε (k * NormedSpace.exp X) := hg
        unfold Formalism.REAL.inUJ at this
        rw [hz] at this
        simpa using this.symm
      have h11 := Formalism.REAL.Jm_mul_self ε
      rw [hJ, Matrix.mul_zero] at h11
      have := congrFun (congrFun h11 ⟨0, hn⟩) ⟨0, hn⟩
      simp at this
  have g4 : (Real.sqrt n * Real.exp t) ^ (-a) ≤ Real.sqrt (Formalism.REAL.hs (k * NormedSpace.exp X)) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos g3 g2 (by linarith)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have g5 : Real.sqrt n ^ a * Real.exp (a / s) * (Real.sqrt n * Real.exp t) ^ (-a) = Real.exp (a / s - a * t) := by
    rw [Real.mul_rpow hsn.le (Real.exp_pos t).le, Real.rpow_neg hsn.le, ← Real.exp_mul, Real.exp_sub,
      show t * -a = -(a * t) by ring, Real.exp_neg]
    have : Real.sqrt n ^ a ≠ 0 := (Real.rpow_pos_of_pos hsn a).ne'
    field_simp
  refine le_trans ?_ (mul_le_mul_of_nonneg_left g4 (by positivity))
  rw [g5]
  unfold decBound
  apply Real.exp_le_exp.2
  rw [hsX, Real.sqrt_sq ht0, ← hq0, ← hs]
  have hc : 0 ≤ h / 8 := by positivity
  have ea : a = h / 8 / s := by rw [ha]; field_simp
  have m1 : a * t - a / s ≤ h / 8 * (t / s) := by
    have : h / 8 * (t / s) = a * t := by rw [ea]; field_simp
    rw [this]
    have : 0 ≤ a / s := by positivity
    linarith
  have m2 : a * t - a / s ≤ h / 8 * t ^ 2 := by
    have e1 : a * t - a / s = h / 8 * (t / s - 1 / s ^ 2) := by rw [ea]; field_simp
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ hc
    have : 0 ≤ (t - 1 / (2 * s)) ^ 2 + 3 / (4 * s ^ 2) := by positivity
    have e2 : (t - 1 / (2 * s)) ^ 2 + 3 / (4 * s ^ 2) = t ^ 2 - t / s + 1 / s ^ 2 := by field_simp; ring
    linarith
  have m3 : a * t - a / s ≤ h / 8 * min (t ^ 2) (t / s) := by
    rcases min_cases (t ^ 2) (t / s) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
    · exact m2
    · exact m1
  linarith

section Conj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]



theorem trace_conj_mul_eq_hilbert_schmidt (g : Matrix (Fin n) (Fin n) ℂ) : (g.conjTranspose * g).trace = ((Formalism.REAL.hs g : ℝ) : ℂ) := by
  unfold Formalism.REAL.hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem hs_unitary_conj (P x : Matrix (Fin n) (Fin n) ℂ) (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Formalism.REAL.hs (P * x * P.conjTranspose) = Formalism.REAL.hs x := by
  have hPP : P.conjTranspose * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hP
  have key : ((P * x * P.conjTranspose).conjTranspose * (P * x * P.conjTranspose)).trace
      = (x.conjTranspose * x).trace := by
    have e : (P * x * P.conjTranspose).conjTranspose * (P * x * P.conjTranspose)
        = P * (x.conjTranspose * x * P.conjTranspose) := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc P * (x.conjTranspose * P.conjTranspose) * (P * x * P.conjTranspose)
          = P * x.conjTranspose * (P.conjTranspose * P) * x * P.conjTranspose := by
            simp only [Matrix.mul_assoc]
        _ = P * (x.conjTranspose * x * P.conjTranspose) := by
            rw [hPP, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc (x.conjTranspose * x), hPP, Matrix.mul_one]
  rw [trace_conj_mul_eq_hilbert_schmidt, trace_conj_mul_eq_hilbert_schmidt] at key
  exact_mod_cast key

end Conj

section Bessel

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]




end Bessel

end Formalism.MainNotions.BridgeLemma

end
