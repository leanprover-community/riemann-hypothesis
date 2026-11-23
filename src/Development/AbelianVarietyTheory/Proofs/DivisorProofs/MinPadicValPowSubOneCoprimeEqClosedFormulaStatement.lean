module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinPadicValPowSubOneCoprimeEqClosedFormula
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateWideInd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes

@[expose] public section

open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.minPadicValPowSubOneCoprime_eq_closedFormula : Formalism.PairingDivisionLocalBalance.MinVal → ∀ l n : ℕ, l.Prime → 2 ≤ n → Even n → mMin l n = Formalism.PairingDivisionLocalBalance.mE l n := by
  first | exact @GlobalTheory.MinValClosed.mMin_eq_mE | exact GlobalTheory.MinValClosed.mMin_eq_mE | (intros; apply GlobalTheory.MinValClosed.mMin_eq_mE <;> assumption)
