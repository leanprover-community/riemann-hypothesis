module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormalisedLocalBesselDatum
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

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_normalised_localBesselDatum : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 1 ≤ k → IsSection k r L.z L.z' μsec → ∃ Bs : B.RealPlaceData k r L.Wp L.Wq, IsStdOf L μsec Bs := by
  first | exact @GlobalTheory.ThA.exists_isStdOf | exact GlobalTheory.ThA.exists_isStdOf | (intros; apply GlobalTheory.ThA.exists_isStdOf <;> assumption)
