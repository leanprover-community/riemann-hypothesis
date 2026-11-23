module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatLogFloorExpLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeTwentyFiveMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem blockAndTorsionExponentBounds_canonicalHubData : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D), GlobalTheory.HubX.Canon L HW R X → 1 ≤ L.sc.L → ∀ c : ℝ, 120 ≤ c → GlobalTheory.HubX.CondCB L X c ∧ KillingConditions.ConstantColumnBound L X c := by
  intro D L HW R X hX hL c hc
  have ht : 1 ≤ D.R.t := D.R.t_odd.pos
  have hn : 1 ≤ D.R.n := D.R.ord_pos
  have hnV : 1 ≤ D.R.nV := by
    show 1 ≤ D.R.r + D.R.t
    omega
  have htR : (1 : ℝ) ≤ D.R.t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn
  have hnVR : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast hnV
  have hN : 1 ≤ 4 * D.R.n * D.R.nV := by
    have := Nat.mul_le_mul hn hnV
    nlinarith
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  have hLg : Formalism.MainNotions.TwistedPlaces.large₂ L = L.sc.L := rfl
  have hL0 : (0 : ℝ) ≤ L.sc.L := by linarith
  refine ⟨?_, ?_⟩
  · intro i _ _ _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.cB]
    have h := GlobalTheory.HubLoc.cBnum_le_thirty (D.nd.l i) D.R.t (4 * D.R.n * D.R.nV) L.sc.L hl ht hN hL
    simp only [cBof, hb, hLg]
    push_cast at h
    have hp : (0 : ℝ) ≤ (D.R.t : ℝ) * D.R.n * D.R.nV * L.sc.L := by positivity
    nlinarith
  · intro i _ _ _ _ u _
    have hl : 2 ≤ D.nd.l i := (D.nd.lPrime i).out.two_le
    rw [hX.c0]
    have h := GlobalTheory.HubLoc.torsionExponent_le_twentyFive_mul (D.nd.l i) (4 * D.R.n * D.R.nV) L.sc.L hl hN hL
    simp only [c0of, hOf, hb, hLg]
    push_cast at h ⊢
    have hp : (0 : ℝ) ≤ (D.R.n : ℝ) * D.R.nV * L.sc.L := by positivity
    nlinarith

end GlobalTheory.HubX
