module

public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPowSmulCompPolyFamilyEigenSu
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

theorem _root_.GlobalTheory.T.capelliEigenfunction_pow_smul_comp_polyFamily_eigenSum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (lam : Fin (2 * r + k + 1) → ℝ) (A₀ : ℝ) (p₀ dA : ℕ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (Aop : B.Mat k r → (Wq' →L[ℂ] Wq)), (∀ s t, s ≠ t → 2 * (((2 * r + 2) * p₀ + dA : ℕ) : ℝ) < |lam s - lam t|) → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A₀) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat k r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq' →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ (((2 * r + 2) * p₀ + dA : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A₀ - (((2 * r + 2) * p₀ + dA : ℕ) : ℝ)) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (fun g => ((Gf k r z z' g ^ p₀ : ℝ) : ℂ) • (f g).comp (Aop g)) g = ∑ i, Fi i g) := by
  first | exact @GlobalTheory.gfPow_smul_comp_polyOp_eigenSum | exact GlobalTheory.gfPow_smul_comp_polyOp_eigenSum | (intros; apply GlobalTheory.gfPow_smul_comp_polyOp_eigenSum <;> assumption)
