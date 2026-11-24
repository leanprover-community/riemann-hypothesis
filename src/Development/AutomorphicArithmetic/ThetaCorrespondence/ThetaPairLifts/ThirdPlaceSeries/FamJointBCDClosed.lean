module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamJointBCD
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNeTypePrimeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointInputAwayFromTypePrimesStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.HTW.LJ
end GlobalTheory.HTW.LJ
namespace GlobalTheory.HTW.RecS
theorem fam_jointBCD_closed_alt : GlobalTheory.Published.FontaineBcris → (∀ D : D7, LocalSituation.adm7 D) → (∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → (∀ D : D7, _root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D) → ∀ {eps : ℝ} (Fm : FamP eps) (R : KillingConditions.RowK), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (j : Fm.Ix x) (HW : HWOf (Fm.D x j).loc) (X : KillingConditions.HubData (Fm.D x j)), _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt (Fm.L x j) → GlobalTheory.PtCore.PtFam (Fm.D x j) X.r X.ρ → KillingConditions.JointParametersHubConditions (Fm.L x j) HW X R := by
  intro hF h7 hFo hJ eps Fm R
  obtain ⟨x0, h⟩ := GlobalTheory.HTW.RecS.fam_jointBCD Fm R h7 hFo
  refine ⟨x0, fun x hx h1 j HW X hA hX => h x hx h1 j HW X (hJ _ _ hA).1 fun i _ hi π hπ => ?_⟩
  refine _root_.GlobalTheory.T.ptIn_of_ptFam_deRham_away hF _ X hX hA.1 i ?_ π hπ
  simp only [TwistedPlaces.gset, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨GlobalTheory.T.inert_prime_ne_typePrime _ _ 0 hi, GlobalTheory.T.inert_prime_ne_typePrime _ _ 1 hi⟩
end GlobalTheory.HTW.RecS
end
