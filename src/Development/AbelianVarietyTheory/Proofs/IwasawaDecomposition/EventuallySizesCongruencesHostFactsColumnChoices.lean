module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyAuxiliaryPlacesSplitDistinctStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyBaseChangeHypothesesColumnChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyCoeffFieldContainsRootOfUnityGroupOrdeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHostEqCompositumTotallyRealImagQuadratStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyHundredLeHermitianRankColumnChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySpacesVDefiniteColumnChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyTwoMulRankLeLevelPrimeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem sizes_host_at_record : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r ∧ (∀ k, 2 * (w.D Z).R.r ≤ (w.D Z).host.g k) ∧ RootsLL (w.D Z) ∧ SphericalInertData.HypEFK (w.D Z) ∧ SphericalInertData.HypCM (w.D Z) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite) ∧ ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  refine EvG.imp (GlobalTheory.T.eventually_hundred_le_hermitianRank_columnChoices.inter (GlobalTheory.T.eventually_two_mul_rank_le_levelPrime.inter (GlobalTheory.T.eventually_coeffField_contains_rootOfUnity_groupOrder.inter (GlobalTheory.T.eventually_host_eq_compositum_totallyReal_imagQuadratic.inter (GlobalTheory.T.eventually_baseChangeHypotheses_columnChoices.inter (GlobalTheory.T.eventually_spacesV_definite_columnChoices.inter GlobalTheory.T.eventually_auxiliary_places_split_distinct)))))) fun K _ _ _ _ H => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H
  exact (h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter h7)))))).imp fun B f T _ G hk T' w Z =>
    ⟨G.1 hk T' w Z, G.2.1 hk T' w Z, G.2.2.1 hk T' w Z, G.2.2.2.1 hk T' w Z, G.2.2.2.2.1 hk T' w Z, G.2.2.2.2.2.1 hk T' w Z,
      G.2.2.2.2.2.2 hk T' w Z⟩

end GlobalTheory.HeightCounting.Up
