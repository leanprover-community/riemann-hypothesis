module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTensorCenterInclusionInjectiveCentralFinran
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.localTensorCenterInclusion_injective_central_finrank : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Function.Injective (iotaF G v) ∧ (∀ z x, Commute (iotaF G v z) x) ∧ Module.finrank (Qv v) (Qv v ⊗[ℚ] G.C) = G.n ^ 2 * Module.finrank (Qv v) (Qv v ⊗[ℚ] G.F) := by
  first | (exact @GlobalTheory.OrbFinAf.iotaF_props) | (exact GlobalTheory.OrbFinAf.iotaF_props) | (intros; apply GlobalTheory.OrbFinAf.iotaF_props  <;> assumption)
