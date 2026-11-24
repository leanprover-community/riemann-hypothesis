module

public import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFCoreC
public import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.NfTieHatSOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaugeConstructionHolds
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

theorem normal_form_hat_compact : CompanionTheory.NFCpt.NFTieHatC := by
  intro Cb
  obtain ⟨Cc, H⟩ := nfTieGen_of Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gauge_construction_holds Cb
  refine ⟨Cc, fun Wp Wq _ _ _ _ _ _ P p hInD => ?_⟩
  obtain ⟨e, L, h1, h2, h3, h4⟩ := H Wp Wq P p hInD
  refine ⟨e, L, h1, h2, h3, fun Y w hw ee Q Lq hS => ?_⟩
  obtain ⟨m, b, u, C, h5, h6, h7⟩ := h4 Y w hw ee Q Lq hS
  exact ⟨m, b, u, C, h5, h6, fun F A hF hcc hA hc => h7 F A hF hcc hA (Or.inr hc)⟩

end Formalism.FourierDecayAlt.P.NormalFormRelations
