module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinKernelLinearAlgebraTrivial
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

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.zarhin_kernel_linearAlgebra_trivial : ∀ (d : ℕ) (GA GB : Type) [CommGroup GA] [CommGroup GB] (f : GA →* GB) (g : GB →* GA), 0 < d → (∀ a, g (f a) = a ^ d) → ∀ (u : Fin 4 → GA) (v : Fin 4 → GB), (∀ i, f (u i) * ∏ j, v j ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ j, f (∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i) * v j ^ d = 1) → ((∀ j, v j = 1) → ∀ j, ∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ i, u i = 1) ∧ ∀ j, v j = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (exact GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (intros; apply GlobalTheory.ZarhinFam.zarhin_kernel_trivial  <;> assumption)
