module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

theorem _root_.GlobalTheory.T.eulerProduct_rankinSelbergGLnGLm_dirichletSeries : ∀ {I : Type} (q : I → ℕ) {n m : ℕ}, m ≤ n → ∀ (α : I → Fin n → ℂˣ) (β : I → Fin m → ℂˣ) (x : ℝ), 1 < x →
    (∀ i, 2 ≤ q i) → GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    ∃ P : ℂ, HasProd (fun i => GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i))
        ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P ∧
      HasSum (fun l : I →₀ (Fin m → ℤ) => l.prod fun i v =>
        GlobalTheory.RSnmUnf.rsTermNM (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v) P := by
  first | (exact @GlobalTheory.RSnmEul.euler_rsTermNM) | (exact GlobalTheory.RSnmEul.euler_rsTermNM) | (intros; apply GlobalTheory.RSnmEul.euler_rsTermNM  <;> assumption)
