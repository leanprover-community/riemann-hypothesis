module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParamCoeffSumBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoversOfLifts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff

@[expose] public section



section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.WtSz
open GlobalTheory.CompHS
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end GlobalTheory.CovTop.WtSz
namespace GlobalTheory.CovTop.WtSz

theorem wts_le_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂} : Set (AllWt.Weight (dat p i))), ∑ τ, ∑ k, |(la τ k : ℝ)| ≤ zBase (Fm.L x ι) ^ 2 * (kap p i / lenT p i PP + 1) := by
  intro hS
  have hL : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (∃ A, SizeAt p i PP A) ∧ (∃ A, HostNum (Fm.D x ι) (Fm.L x ι) PP A 10) ∧
      WtNum p i PP := by
    refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and hS (Formalism.MainNotions.Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 10) _root_.GlobalTheory.CovTop.WtShape.wtN_z))
      fun Fm CH _ h => ?_
    obtain ⟨⟨C1, _, a1, ha1⟩, ⟨C2, _, a2, ha2⟩, ⟨C3, _, a3, ha3⟩⟩ := h
    exact ⟨0, le_rfl, max a1 (max a2 a3), fun x hx hle ι p hp i =>
      ⟨⟨C1, ha1 x hx ((le_max_left _ _).trans hle) ι p hp i⟩,
        ⟨C2, ha2 x hx (((le_max_left _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩,
        ha3 x hx (((le_max_right _ _).trans (le_max_right _ _)).trans hle) ι p hp i⟩⟩
  exact _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt hL fun Fm x hx ι p i _ _ h hi _ _ =>
    at_pt p i _ h.1.choose h.2.1.choose hi h.1.choose_spec h.2.1.choose_spec h.2.2
end GlobalTheory.CovTop.WtSz
end
end
