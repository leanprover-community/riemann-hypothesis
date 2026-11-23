module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWCOnPtOfGuardedStatement
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
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem evWC_fun_of_fun0Fit_alt : ∀ Fld : GlobalTheory.BigTop.Fun.FldT, _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits @Fld → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm) → EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ → EvW (fun _ _ _ b => GlobalTheory.BigTop.Fun.HasGrid @Fld b.pt CF) 𝒜 σ → EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandFunctionalBound 𝒜 σ := by
  intro Fld h
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun CF hCF 𝒜 σ hD hR hG => ?_⟩
  exact _root_.GlobalTheory.T.eventually_onPt_of_pDiv_ties_and_onPt (fun Fm => DIVinN Fm) (fun _ _ _ p => GlobalTheory.BigTop.Fun.HasGrid @Fld p CF)
    (fun C CH _ _ _ p => (p.S false).FUN (p.N C CH))
    ((h CF hCF).imp fun Fm CH _ a hN =>
      ⟨0, le_rfl, _root_.GlobalTheory.BigTop.Fun.evPt_mono (a hN) fun _ _ _ _ _ b hg C _ => b hg C⟩) 𝒜 σ hD hR hG
end GlobalTheory.Fc.Ind
end
