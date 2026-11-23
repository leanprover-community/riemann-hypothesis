module

public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
public import Formalism.HermitianCurvature.HerGenC
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionPointwiseBoundOfDifferentTyp
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

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.capelliEigenfunction_pointwiseBound_of_differentTypes : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ C C₃ C₀ : ℝ, 0 ≤ C → 0 ≤ C₃ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b c A₀ : ℝ) (n₀ p₀ : ℕ) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ), StdNum C b c P lam → (n₀ = 0 ∧ ∃ l ∈ Finset.Icc 1 P.k, ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u l - P.u' l|) → 3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → EigDec f A₀ lam' → Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c - 1) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  first | exact @GlobalTheory.capelliEigenfunction_pointwiseBound_of_differentTypes.thmBp_eigen_different_types | exact GlobalTheory.capelliEigenfunction_pointwiseBound_of_differentTypes.thmBp_eigen_different_types | (intros; apply GlobalTheory.capelliEigenfunction_pointwiseBound_of_differentTypes.thmBp_eigen_different_types <;> assumption)
