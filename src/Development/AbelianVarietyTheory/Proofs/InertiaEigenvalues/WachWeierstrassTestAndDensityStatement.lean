module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

theorem _root_.GlobalTheory.T.wachWeierstrass_test_and_density : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; (∀ (k : ℕ) (a : AA K LL), (∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → a ∈ van W i ζ k) → W.Q ^ k ∣ a) ∧ (∀ (k : ℕ) (a : AA K LL), (∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → a ∈ van W i ζ k) → W.X ^ k ∣ a) ∧ (∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ (f : PowerSeries ↥LL.1) (m : ℕ), ∃ (a : AA K LL) (c : ↥LL.1), c ≠ 0 ∧ PowerSeries.X ^ m ∣ c • W.lev i ζ a - f) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∀ (f : PowerSeries ↥LL.1) (m : ℕ), ∃ (a : AA K LL) (c : ↥LL.1), c ≠ 0 ∧ PowerSeries.X ^ m ∣ c • W.lev i ζ a - f ∧ ∀ (i' : Let K) (ζ' : ↥LL.1), IsPrimitiveRoot ζ' (l ^ s) → (i', ζ') ≠ (i, ζ) → a ∈ van W i' ζ' m := by
  first | exact @GlobalTheory.NL.WDiv.weierstrass_dense | exact GlobalTheory.NL.WDiv.weierstrass_dense | (intros; apply GlobalTheory.NL.WDiv.weierstrass_dense <;> assumption)
