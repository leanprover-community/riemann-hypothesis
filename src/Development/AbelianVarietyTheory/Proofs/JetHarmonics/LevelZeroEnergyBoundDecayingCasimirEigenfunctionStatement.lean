module

public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimE
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyBoundDecayingCasimirEigenfunction
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

theorem _root_.GlobalTheory.T.levelZeroEnergyBound_decayingCasimirEigenfunction : GlobalTheory.HCXi.BesselXiIntegrable → (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ), B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + 0 : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd p nn (Formalism.FourierDecayAlt.P.TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N) ∧ (∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (P : M.Par) (u u' : ℕ → ℝ) (q : KB.Pl (Formalism.FourierDecayAlt.P.CutBP2.shP P u u') Wp Wq') (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (cs A₀ : ℝ) (p₀ dA : ℕ) (nn : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (Y : Finset ℝ) (N : ℕ), (∃ (n₁ : ℕ) (c : Fin n₁ → B.Mat P.k P.r → ℂ) (L : Fin n₁ → (Wq' →L[ℂ] Wq)), (∀ i, U.IsPolyDeg dA (c i)) ∧ ∀ g, Aop g = ∑ i, c i g • L i) → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) → (∀ Y : ℝ, ∀ g ∈ B.GV P.k P.r, Q.CV P.k P.r (Y : ℂ) (f) g = ((∏ s, (Y + lam' s) : ℝ) : ℂ) • (f) g) → (∀ s t, s ≠ t → 2 * cs ≤ |lam s - lam t|) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) ≤ cs - 1) → B.AB P.k P.r ≤ A₀ - (((2 * P.r + 2) * p₀ + dA : ℕ) : ℝ) → (∀ y : ℝ, ∏ s, (|y + lam s| + cs) ≤ nn y) → Formalism.FourierDecayAlt.P.CutBP.LimBd q nn (Formalism.FourierDecayAlt.P.CutBP2.fpmSh q f Aop p₀) Y N) := by
  first | exact @GlobalTheory.limBd_fpm_and_fpmSh | exact GlobalTheory.limBd_fpm_and_fpmSh | (intros; apply GlobalTheory.limBd_fpm_and_fpmSh <;> assumption)
