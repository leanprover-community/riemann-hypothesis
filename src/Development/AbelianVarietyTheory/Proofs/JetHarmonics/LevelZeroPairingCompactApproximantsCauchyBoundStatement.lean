module

public import Formalism.HermitianCurvature.StatementD
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCompactApproximantsCauchyBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.GlobalTheory.T.levelZeroPairing_compactApproximants_cauchy_bound : ∃ Cc : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (N : ℕ), C6.IsCut0 χ → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → Tendsto (fun n : ℕ => B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₂ g))) atTop (𝓝 (B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((D.cutF Bs χ f ε₁)) w) (D.cutF Bs χ f ε₂))) ∧ ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g))‖ ≤ K / ((n : ℝ) + 1) := by
  first | exact @GlobalTheory.LevelZeroApprox.beta_approx | exact GlobalTheory.LevelZeroApprox.beta_approx | (intros; apply GlobalTheory.LevelZeroApprox.beta_approx <;> assumption)
