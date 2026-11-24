module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusCongrOfFiniteOfLocalDividedPower
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.frobenius_congr_of_finite_of_local_dividedPower : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (w : ℕ × ℕ → Wq l a) (s : Finset (ℕ × ℕ)), ofW t K e (fun p => if p ∈ s then w p else 0) ∈ GoodSet t e φ₂) → (∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (φ₂ G)) = coeff n (coeff i (φ₂ H))) → (∀ (i n : ℕ) (G H : K⟦X⟧⟦X⟧), (∀ i' ≤ i, ∀ n' ≤ n, coeff n' (coeff i' G) = coeff n' (coeff i' H)) → coeff n (coeff i (G ^ l)) = coeff n (coeff i (H ^ l))) → ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.goodSet_of_finite_of_local | exact GlobalTheory.CrysPrism.goodSet_of_finite_of_local | (intros; apply GlobalTheory.CrysPrism.goodSet_of_finite_of_local <;> assumption)
