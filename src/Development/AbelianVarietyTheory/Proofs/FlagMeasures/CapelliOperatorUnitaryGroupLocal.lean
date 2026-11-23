module

import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.Transport
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.SmRight
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.CapelliHighestWeightConjugated
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CapelliLocality

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma exp_inUH (H K Y : Matrix (Fin n) (Fin n) ℂ) (hKH : K * H = 1) (hHK : H * K = 1)
    (hY : Yᴴ * H = -(H * Y)) : inUH H (NormedSpace.exp Y) := by
  have h1 : Yᴴ = H * (-Y) * K := by
    calc Yᴴ = Yᴴ * H * K := by rw [Matrix.mul_assoc, hHK, Matrix.mul_one]
      _ = H * (-Y) * K := by rw [hY, Matrix.mul_neg]
  unfold inUH
  rw [← Matrix.exp_conjTranspose, h1, ioh_exp_conj H K (-Y) hKH hHK]
  have h2 : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  calc H * NormedSpace.exp (-Y) * K * H * NormedSpace.exp Y
      = H * (NormedSpace.exp (-Y) * (K * H) * NormedSpace.exp Y) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [hKH, Matrix.mul_one, h2, Matrix.mul_one]

lemma inUH_mul {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : inUH H a) (hb : inUH H b) : inUH H (a * b) := by
  unfold inUH at *
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha, hb]

lemma rdV_congr (H K X : Matrix (Fin n) (Fin n) ℂ) (hKH : K * H = 1) (hHK : H * K = 1)
    (hX : Xᴴ * H = -(H * X)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUH H g) :
    RdV X F₁ g = RdV X F₂ g := by
  unfold RdV
  congr 1
  funext t
  refine hF _ (inUH_mul hg (exp_inUH H K _ hKH hHK ?_))
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hX, smul_neg]
  simp

lemma hpart1_mem (H Z : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) : (hpart1 H Z)ᴴ * H = -(H * hpart1 H Z) := by
  have hi : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  have e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H := by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]
  unfold hpart1
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hi, hH,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_assoc, hKH, e, Matrix.mul_one]
  rw [← smul_neg, neg_sub]
  simp

lemma hpart2_mem (H Z : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) : (hpart2 H Z)ᴴ * H = -(H * hpart2 H Z) := by
  have hi : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  have e : H * (H⁻¹ * (Zᴴ * H)) = Zᴴ * H := by rw [← Matrix.mul_assoc, hHK, Matrix.one_mul]
  have hs : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  unfold hpart2
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hi, hH,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, hKH, e, Matrix.mul_one]
  rw [hs, neg_smul, add_comm]

lemma foldr_congr (H : Matrix (Fin n) (Fin n) ℂ) (hKH : H⁻¹ * H = 1) (hHK : H * H⁻¹ = 1)
    (hH : Hᴴ = H) (l : List (ℂ × Fin n × Fin n)) {F₁ F₂ : Matrix (Fin n) (Fin n) ℂ → E}
    (hF : ∀ x, inUH H x → F₁ x = F₂ x) :
    ∀ x, inUH H x →
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ x =
      (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ x := by
  induction l with
  | nil => simpa using hF
  | cons p l ih =>
    intro x hx
    simp only [List.map_cons, List.foldr_cons]
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₁ = G₁ at ih ⊢
    generalize (l.map fun p => Formalism.QuantumDeterminants.Top (EabH H) p.1 p.2.1 p.2.2).foldr (fun T h => T h) F₂ = G₂ at ih ⊢
    unfold Formalism.QuantumDeterminants.Top EabH
    rw [ih x hx, rdV_congr H H⁻¹ _ hKH hHK (hpart1_mem H _ hKH hHK hH) ih hx,
      rdV_congr H H⁻¹ _ hKH hHK (hpart2_mem H _ hKH hHK hH) ih hx]

theorem capelliH_local : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  apply CompanionTheory.CapEig.capelli_localization <;> assumption

end GlobalTheory.CapelliLocality

end
