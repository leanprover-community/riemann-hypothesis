module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
public import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointHalfLevelLift
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier

@[expose] public section



section
section

noncomputable section
section Point
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix Formalism.L2.Theta Formalism.IndefR
open scoped TensorProduct
namespace GlobalTheory.NeatOne
end GlobalTheory.NeatOne
end Point
section Family
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open Formalism.IndefR.FWT
namespace GlobalTheory.NeatOne
theorem neat_divisor_free_half_lifts_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
      (fun h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k => (p.O i).lev2 ((p.R.eG.trans p.cG).symm (h : G0g (Fm.D x ι).nd))) := by
  intro _ _
  refine Formalism.MainNotions.Closed.imp (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 6) fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i _ k => free_half p i (rank_add_one_lt Fm x hx ι _ C (ha x hx hle ι p hp i)) k⟩
end GlobalTheory.NeatOne
end Family
end
end
section

theorem _root_.GlobalTheory.T.freePt_lev2_halfH_at_last_index : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
      (fun h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k => (p.O i).lev2 ((p.R.eG.trans p.cG).symm (h : G0g (Fm.D x ι).nd))) := by
  first | exact @_root_.GlobalTheory.NeatOne.neat_divisor_free_half_lifts_alt | exact _root_.GlobalTheory.NeatOne.neat_divisor_free_half_lifts_alt | (intros; apply _root_.GlobalTheory.NeatOne.neat_divisor_free_half_lifts_alt <;> assumption)
end
end
