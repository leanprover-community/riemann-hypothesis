module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TraceSum
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.InducedCmType
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
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
import Mathlib.RingTheory.PicardGroup
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

namespace Formalism.MainNotions.Ext

theorem embT_injective (D : D7) : Function.Injective (embT D) := by
  intro τ τ' h
  have h1 := (factEmb D.R D.host).1.1 h
  exact D.eTau.injective (Subtype.ext h1)

theorem card_Tau_eq (D : D7) : Fintype.card D.what₂.Tau = Module.finrank D.host.K D.host.E := by
  have h1 := Module.finrank_mul_finrank ℚ D.host.K D.host.E
  rw [Formalism.MainNotions.Ext.finrank_K D.host, Formalism.MainNotions.StandardLattice.finrank_host D] at h1
  rw [D.what₂.card_Tau]
  omega

theorem trace_sum_over_letters (H : TraceSum) (D : D7) : StandardLatticesGL3.TraceMapNormalisation D :=
  H D.host.E D.host.K D.host.φ₀ D.what₂.Tau (embT D) (embT_injective D) (GL3Theta.induced_cm_type D) (card_Tau_eq D)

end Formalism.MainNotions.Ext
