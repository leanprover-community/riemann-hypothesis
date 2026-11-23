module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GBigAtTiedStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QnNotMemStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValBoundTwistedStatement
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
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
noncomputable section
namespace GlobalTheory.ThmAUpper
theorem thmA_upper_alt : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint →
    (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → FieldDat → TorEx →
    (_root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) := by
  intro hG hS hdl hF hT
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono (_root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hdl hF) (_root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hdl hT)) ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH hp hd
  refine ⟨hd, fun ⟨hf, ht⟩ w hw => ⟨_root_.GlobalTheory.T.qn_not_mem_asIdeal_of_mu_ne p CF d hp hd w hw, fun l hl hlw i j s Λ Λd z hs1 hs2 hΛ hΛd hz => ?_⟩⟩
  have hw' : D.plEq (D.plEq.symm w) = w := D.plEq.apply_symm_apply w
  have hl' : D.what₂.places.resChar (D.plEq.symm w) = l := resChar_eq _ hl (by rw [hw']; exact hlw)
  have key := _root_.GlobalTheory.T.cm_abelian_field_data_of_toric_ratio_alt p CF d hp hd hG hf ht (D.plEq.symm w) (xiH_twisted p w hw).1 i j s Λ Λd z hs1 hs2
    (by rw [← nuH_twisted p d.G w hw]; exact hΛ) (by rw [hl']; exact hΛd) hz
  rw [hw', hl'] at key
  exact key
end GlobalTheory.ThmAUpper
end
end
