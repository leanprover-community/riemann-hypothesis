module

public import Formalism.LocalRingCardinality.DataTies
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGap
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.formalDegree_eq_harishChandra_of_gap : ∀ (D : D7), Ties D → ∀ (τ : D.what₂.Tau) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) → Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ)) h → Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h → D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) :=
  GlobalTheory.dsig_eq_fdegHC_of_gap
