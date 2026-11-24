module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFiveFactorsHermitianVolume
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.prod_five_factors_hermitian_volume : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (p q a : ℕ) (j : Fin a → ℕ), ∑ i, j i ≤ q → 2 * q + 2 ≤ p + q → cIw p q j ^ Formalism.HermitianLatticesTheory.fDeg E * (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * dimN (p + q) j / 2) * (∏ i, 2 ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j i ^ 2) * ∏ l ∈ Finset.Icc 2 (j i), zetaE E l)) / ∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), rankFac E M = kapBd E p q j := by
  first | exact @GlobalTheory.FiveFactors.prod_five_factors | exact GlobalTheory.FiveFactors.prod_five_factors | (intros; apply GlobalTheory.FiveFactors.prod_five_factors <;> assumption)
