module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigTop.Fun
theorem gBig_atTied_alt : ∀ Q : GlobalTheory.SqTop.GP, _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.SqTop.GBig @Q → _root_.GlobalTheory.BigTop.Fun.LeafConditions (@Fitted @Comparison₂) fun p _ d C _ => Q d.G p.P.A3.A.μ0 C p.Z.x p.Z.b := by
  intro Q hS hD hG
  obtain ⟨CF0, hG⟩ := hG
  refine ⟨CF0, fun CF hCF => (hS.and hD).imp fun {eps} Fm CH he h => ?_⟩
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩⟩ := h
  intro _
  obtain ⟨C0, x₀, hC⟩ := hG eps CF hCF
  refine ⟨C0, fun C hC0 => ⟨max x₀ (max x1 x2), fun x hx hle i p hp d hd => ?_⟩⟩
  obtain ⟨_, a, ht⟩ := hd
  have hset := h1 x hx (le_of_max_le_left (le_of_max_le_right hle)) i p hp ht.ok.eser
  have hdl := h2 x hx (le_of_max_le_right (le_of_max_le_right hle)) i p hp
  have hx0 : x₀ ≤ (Fm.L x i).sc.x := (le_of_max_le_left hle).trans (Fm.L_x x i hx).ge
  exact hC C hC0 _ (Fm.L x i) (Fm.L_eps x i) hx0 ⟨hset.size, hset.host, hset.hF, hdl⟩ _ p.R.toLevCh p.P.A3.A.μ0
    hset.core.lev d.G
end GlobalTheory.BigTop.Fun
end
end
