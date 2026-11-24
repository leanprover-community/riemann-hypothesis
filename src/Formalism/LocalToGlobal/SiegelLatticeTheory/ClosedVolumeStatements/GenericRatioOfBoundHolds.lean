module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.FourParts
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Corank
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
public import Formalism.PeriodIntegrals.PairCorankPos
public import Formalism.PadicSubsetSums.StableGradedCounts.MemBesselSetZeroIffUpperTriangular
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.BetaIndep
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DCRelEquiv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMatBound
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGMirBound
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdCellInS
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSClassConst
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InSRelevant
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PairCorankPos
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalEquivGen
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalRelRepFree
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScalarPairDr
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermAttrConst
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermCarrierStable
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WhitFunctDual
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

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Closed

section Terms

variable (D : D7) (u u' : D.what₂.Word)

theorem TermEqIff_holds : Formalism.L2.SG.TermDef.TermEqIff D u u' := term_eq_iff_relation D u u'
theorem TermStable_holds : Formalism.L2.SG.TermDef.TermStable D u u' := term_carrier_stable D u u'
theorem TermFun_holds : Formalism.L2.SG.TermDef.TermFun D u u' := term_function_const D u u'

theorem TermInSFun_holds : Formalism.L2.SG.FourParts.TermInSFun D u u' := in_s_class_constant D u u'
theorem TermInSRel_holds : Formalism.L2.SG.FourParts.TermInSRel D u u' := in_s_relevant D u u'
theorem TermIdIffInS_holds : Formalism.L2.SG.FourParts.TermIdIffInS D u u' := term_id_iff_in_s D u u'

theorem ScalarEquiv_holds : Formalism.L2.SG.Corank.ScalarEquiv D u u' := Formalism.L2.SG.Corank.scalarEquiv_of_G (D := D) scalar_equiv_general u u'
theorem ScalarRepFree_holds : Formalism.L2.SG.Corank.ScalarRepFree D u u' := scalar_rep_free D u u'
theorem BetaFree_holds : Formalism.L2.SG.Corank.BetaFree D u u' := scalPairs_betaFree D u u'

theorem ScalarDr_holds : Formalism.L2.SG.Corank.ScalarDr D u u' := by
  intro F0 what₂ hrows p hp
  exact scalar_pair_dr D u u' F0 what₂ hrows p.lam p.mem p.fst p.snd p.G_fst p.G_snd p.beta p.isPair
    hp.1 hp.2

end Terms

theorem CorankPosG_holds : PI.PairCorankPos.CorankPosG := pair_corank_pos
theorem ScalarEquivG_holds : Formalism.L2.SG.Corank.ScalarEquivG := scalar_equiv_general

theorem GelfandGraevMultOne_holds : Formalism.L2.SG.GGMirabolic.GelfandGraevMultOne := whittaker_functional_dual Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.gelfand_graev_multiplicity_one
theorem MirabolicBound_holds : Formalism.L2.SG.GGMirabolic.MirabolicBound := mirabolic_bound
theorem GGMatrixBoundOfLit_holds : Formalism.L2.SG.GGMirabolic.GGMatrixBoundOfLit := gg_matrix_bound
theorem GGMatrixBound_holds : Formalism.L2.SG.GGMirabolic.GGMatrixBound :=
  GGMatrixBoundOfLit_holds GelfandGraevMultOne_holds MirabolicBound_holds
theorem TermsGGBound_holds : Formalism.L2.SG.GGMirabolic.TermsGGBound :=
  Formalism.L2.SG.GGMirabolic.termsGGBound_of_matrix GGMatrixBound_holds

theorem IsSplitRow_holds (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ) :
    Formalism.L2.SG.Saturated.IsSplitRow D F0 Λ := split_row_iso D u F0 Λ hΛ

end Formalism.L2.SG.Closed
