module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormula
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
namespace LeafFixedPointPairing
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw matLat)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.IndefR.Datum Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
namespace GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
theorem fp_tie_alt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → FinK → AwayK → _root_.GlobalTheory.BigTop.Fun.LeafFixedPoint @Comparison₂ := by
  intro hS hF hA
  obtain ⟨c1, hF⟩ := hF
  obtain ⟨c2, hA⟩ := hA
  refine ⟨max c1 c2, fun CF hCF => ?_⟩
  obtain ⟨C1, hF⟩ := hF CF ((le_max_left _ _).trans hCF)
  obtain ⟨C2, hA⟩ := hA CF ((le_max_right _ _).trans hCF)
  refine hS.imp fun {eps} Fm _ _ a _ => ⟨max (max C1 C2) (max CF 0), fun C hC => ?_⟩
  obtain ⟨x₁, a⟩ := a
  have hC1 : C1 ≤ C := ((le_max_left _ _).trans (le_max_left _ _)).trans hC
  have hC2 : C2 ≤ C := ((le_max_right _ _).trans (le_max_left _ _)).trans hC
  have hCF' : CF ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans hC
  have hC0 : 0 ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans hC
  obtain ⟨x₂, hF⟩ := hF eps C hC1
  obtain ⟨x₃, hA⟩ := hA eps C hC2
  refine ⟨max x₁ (max x₂ x₃), fun x hx hle i p hp d hd => ?_⟩
  obtain ⟨-, b, hT⟩ := hd
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans hle
  have hx₂ : x₂ ≤ (Fm.L x i).sc.x := ((le_max_left _ _).trans ((le_max_right _ _).trans hle)).trans (Fm.L_x x i hx).ge
  have hx₃ : x₃ ≤ (Fm.L x i).sc.x := ((le_max_right _ _).trans ((le_max_right _ _).trans hle)).trans (Fm.L_x x i hx).ge
  have hset := a x hx hx₁ i p hp hT.ok.eser
  exact leaf_at hT hC0 hCF'
    (hF _ (Fm.L x i) (Fm.L_eps x i) hx₂ _ _ _ _ _ _ _ hset b.ch hT.ok.is b.atScale hT.ok.field)
    (hA _ (Fm.L x i) (Fm.L_eps x i) hx₃ _ _ _ _ _ _ _ hset b.ch hT.ok.is b.atScale hT.ok.field)
end GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm
end
end
end LeafFixedPointPairing
section
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
theorem _root_.GlobalTheory.Adopt.leafFixedPoint_of_finK_awayK : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → FinK → AwayK → _root_.GlobalTheory.BigTop.Fun.LeafFixedPoint @Comparison₂ := by
  first | exact @_root_.LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.fp_tie_alt | exact _root_.LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.fp_tie_alt | (intros; apply _root_.LeafFixedPointPairing.GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm.fp_tie_alt <;> assumption)
end
end
