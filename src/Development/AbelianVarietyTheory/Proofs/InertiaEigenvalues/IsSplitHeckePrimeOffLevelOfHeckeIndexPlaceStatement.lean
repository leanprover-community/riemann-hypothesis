module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlace
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie

theorem _root_.GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace : ∀ (D : D7) (T0 : CoreJ D), LawsJ T0 → ∀ (i : D.ntw.Tw) (k : ℕ) (P : PlE D.host), Formalism.MainNotions.IntegralHeckeForms.HkIdx (X := D.ntw) i k P → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime T0.Q.H T0.Q.l P.asIdeal (charAt P) ∧ charAt P ≠ D.ntw.l i := by
  first | exact @GlobalTheory.HeckeIndexPrime.isHeckePrime_of_hkIdx | exact GlobalTheory.HeckeIndexPrime.isHeckePrime_of_hkIdx | (intros; apply GlobalTheory.HeckeIndexPrime.isHeckePrime_of_hkIdx <;> assumption)
