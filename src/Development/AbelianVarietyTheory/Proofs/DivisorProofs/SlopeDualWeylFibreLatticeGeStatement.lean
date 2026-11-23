module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeDualWeylFibreLatticeGe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

theorem _root_.GlobalTheory.T.slope_dualWeylFibreLattice_ge : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (s : (K →+* ℂ) → ℝ) (X : (K →+* ℂ) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → (∀ σ, 0 < s σ) → (∀ σ t, (X σ t).det ≠ 0) → (∀ σ, s ((starRingEnd ℂ).comp σ) = s σ) → (∀ σ t, ‖(X ((starRingEnd ℂ).comp σ) t).det‖ = ‖(X σ t).det‖) → (∀ σ, (fibY la (s σ) (X σ)).det ≠ 0) ∧ lineDeg s (fun w => (vAdd w (a w) : ℝ)) + ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * detDeg (fun w => B w t) (fun σ => X σ t) - Real.log (dim (la t)) / 2) ≤ slope_sq (matNorm fun σ => fibY la (s σ) (X σ)) (locLat fun w => fibA la (a w) (B w)) / 2 := by
  first | exact @GlobalTheory.FibSlope.slope_fibre_ge | exact GlobalTheory.FibSlope.slope_fibre_ge | (intros; apply GlobalTheory.FibSlope.slope_fibre_ge <;> assumption)
