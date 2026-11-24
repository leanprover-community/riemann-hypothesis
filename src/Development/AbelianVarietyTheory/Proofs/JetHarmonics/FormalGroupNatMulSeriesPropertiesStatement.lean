module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
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

@[expose] public section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.formalGroupNatMulSeries_properties : ∀ (R : Type) [CommRing R] (F : FormalGroup R), (∀ n, PowerSeries.constantCoeff (nMul F n) = 0 ∧ PowerSeries.coeff 1 (nMul F n) = (n : R)) ∧ nMul F 1 = PowerSeries.X ∧ (∀ i j, MvPowerSeries.subst (![nMul F i, nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries = nMul F (i + j)) ∧ (∀ i j, (nMul F i).subst (nMul F j) = nMul F (i * j)) ∧ (∀ (S : Type) [CommRing S] (φ : R →+* S) (n : ℕ), PowerSeries.map φ (nMul F n) = nMul (F.map φ) n) := by
  first | exact @GlobalTheory.ConvSer.nMul_props | exact GlobalTheory.ConvSer.nMul_props | (intros; apply GlobalTheory.ConvSer.nMul_props <;> assumption)
