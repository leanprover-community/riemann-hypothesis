module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg

@[expose] public section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegCov

section Ring

variable {A : Type} [CommRing A]

theorem cT_mul (τ : A →+* A) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) A)
    (y : Matrix (Fin b) (Fin c) A) : cT τ (x * y) = cT τ y * cT τ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (τ : A →+* A) {a : ℕ} : cT τ (1 : Matrix (Fin a) (Fin a) A) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]

theorem cT_cT (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) {a b : ℕ} (x : Matrix (Fin a) (Fin b) A) :
    cT τ (cT τ x) = x := by
  unfold cT
  ext i j
  exact hτ (x i j)

def covEquiv (τ : A →+* A) {m n : ℕ} (G G' : Matrix (Fin n) (Fin n) A)
    (P P' : Matrix (Fin m) (Fin m) A) (hG : G * G' = 1) (hG' : G' * G = 1)
    (hP : P * P' = 1) (hP' : P' * P = 1) :
    Matrix (Fin m) (Fin n) A ≃ Matrix (Fin m) (Fin n) A where
  toFun x := P' * x * cT τ G'
  invFun y := P * y * cT τ G
  left_inv x := by
    have h : cT τ G' * cT τ G = 1 := by rw [← cT_mul, hG, cT_one]
    calc P * (P' * x * cT τ G') * cT τ G = (P * P') * x * (cT τ G' * cT τ G) := by
          simp only [Matrix.mul_assoc]
      _ = x := by rw [hP, h, Matrix.one_mul, Matrix.mul_one]
  right_inv y := by
    have h : cT τ G * cT τ G' = 1 := by rw [← cT_mul, hG', cT_one]
    calc P' * (P * y * cT τ G) * cT τ G' = (P' * P) * y * (cT τ G * cT τ G') := by
          simp only [Matrix.mul_assoc]
      _ = y := by rw [hP', h, Matrix.one_mul, Matrix.mul_one]

theorem eq_of_conj (τ : A →+* A) {n : ℕ} {h D g g' : Matrix (Fin n) (Fin n) A}
    (hg : g * g' = 1) (hD : cT τ g * h * g = D) : h = cT τ g' * D * g' := by
  have hg2 : cT τ g' * cT τ g = 1 := by rw [← cT_mul, hg, cT_one]
  rw [← hD]
  calc h = (cT τ g' * cT τ g) * h * (g * g') := by
        rw [hg2, hg, Matrix.one_mul, Matrix.mul_one]
    _ = cT τ g' * (cT τ g * h * g) * g' := by simp only [Matrix.mul_assoc]

theorem trace_cov (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) {m n : ℕ}
    (D g' : Matrix (Fin n) (Fin n) A) (E p' : Matrix (Fin m) (Fin m) A)
    (x : Matrix (Fin m) (Fin n) A) :
    Matrix.trace ((cT τ g' * D * g') * (cT τ x * (cT τ p' * E * p') * x)) =
      Matrix.trace (D * (cT τ (p' * x * cT τ g') * E * (p' * x * cT τ g'))) := by
  rw [cT_mul, cT_mul, cT_cT τ hτ]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (cT τ g')]
  simp only [Matrix.mul_assoc]

end Ring

section Red

variable {R : Type} [CommRing R]

theorem red_mul (ϖ : R) (k : ℕ) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R)
    (y : Matrix (Fin b) (Fin c) R) : red ϖ k (x * y) = red ϖ k x * red ϖ k y := by
  unfold red
  exact Matrix.map_mul

theorem red_cT (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) R) : red ϖ k (cT σ x) = cT (barσ σ ϖ hf k) (red ϖ k x) := by
  ext i j
  exact (barσ_mk σ ϖ hf k (x j i)).symm

theorem red_one (ϖ : R) (k : ℕ) {a : ℕ} : red ϖ k (1 : Matrix (Fin a) (Fin a) R) = 1 := by
  unfold red
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem barσ_inv (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (hσ : ∀ a, σ (σ a) = a) (k : ℕ)
    (a : R ⧸ lev ϖ k) : barσ σ ϖ hf k (barσ σ ϖ hf k a) = a := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [barσ_mk, barσ_mk, hσ]

end Red

theorem gauss_cov (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ)
    (hσ : ∀ a, σ (σ a) = a) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ)
    (m n : ℕ) (h D g g' : Matrix (Fin n) (Fin n) R) (S E p p' : Matrix (Fin m) (Fin m) R)
    (hg : g * g' = 1) (hg' : g' * g = 1) (hp : p * p' = 1) (hp' : p' * p = 1)
    (hD : cT σ g * h * g = D) (hE : cT σ p * S * p = E) :
    (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
        χ (Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)))) =
      ∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
        χ (Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) y * red ϖ k E * y))) := by
  have hh : h = cT σ g' * D * g' := eq_of_conj σ hg hD
  have hS : S = cT σ p' * E * p' := eq_of_conj σ hp hE
  have rg : red ϖ k g * red ϖ k g' = 1 := by rw [← red_mul, hg, red_one]
  have rg' : red ϖ k g' * red ϖ k g = 1 := by rw [← red_mul, hg', red_one]
  have rp : red ϖ k p * red ϖ k p' = 1 := by rw [← red_mul, hp, red_one]
  have rp' : red ϖ k p' * red ϖ k p = 1 := by rw [← red_mul, hp', red_one]
  refine Fintype.sum_equiv
    (covEquiv (barσ σ ϖ hf k) (red ϖ k g) (red ϖ k g') (red ϖ k p) (red ϖ k p') rg rg' rp rp')
    _ _ ?_
  intro x
  have key : Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)) =
      Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) (red ϖ k p' * x * cT (barσ σ ϖ hf k) (red ϖ k g')) *
        red ϖ k E * (red ϖ k p' * x * cT (barσ σ ϖ hf k) (red ϖ k g')))) := by
    rw [hh, hS, red_mul, red_mul, red_mul, red_mul, red_cT σ ϖ hf, red_cT σ ϖ hf]
    exact trace_cov (barσ σ ϖ hf k) (barσ_inv σ ϖ hf hσ k) (red ϖ k D) (red ϖ k g') (red ϖ k E)
      (red ϖ k p') x
  exact congrArg (⇑χ) key

end GlobalTheory.CompanionTheory.SiegCov
