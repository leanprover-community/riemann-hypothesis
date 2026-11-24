module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProofStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientMeasureIntegrationFormulasUnimodularStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabSelfDualLatticeTransitiveOnLengthStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryUnfoldingVolumeVectorStabilizerStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.UnfoldingObj

theorem unfolding : ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding.Unfolding D := fun D =>
  (GlobalTheory.UnfoldingCompare.unfolding_iff D).1 (GlobalTheory.T.unitaryUnfolding_volume_vectorStabilizer GlobalTheory.T.quotientMeasure_integration_formulas_unimodular GlobalTheory.T.adelicUnitaryGroupHaarProperties_proof GlobalTheory.T.stabSelfDualLattice_transitive_on_length D)

end GlobalTheory.UnfoldingObj
