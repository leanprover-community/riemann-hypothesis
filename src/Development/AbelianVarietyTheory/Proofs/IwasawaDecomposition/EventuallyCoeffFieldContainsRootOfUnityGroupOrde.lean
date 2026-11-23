module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem isAlgebraic_exp_two_pi_div (n : ℕ) (hn : 0 < n) :
    IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I / n)) :=
  (((Complex.isPrimitiveRoot_exp n hn.ne').isIntegral hn).tower_top (A := ℚ)).isAlgebraic

theorem rootsLL_evLgG :
    EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), RootsLL (w.D Z) := by
  have hLg : ∀ K : Ctx, large₂ K fun B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), RootsLL (w.D Z) := by
    intro K
    refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅,
      fun B _ _ _ _ => {Complex.exp (2 * Real.pi * Complex.I / B.restRowsFiniteGroupCard)}, by simp, ?_, ?_⟩
    · intro B _ _ _ _ z hz
      rw [Finset.mem_singleton] at hz
      subst hz
      exact isAlgebraic_exp_two_pi_div _ B.restRowsFiniteGroupCard_pos
    · intro B f T₀ _ hH _ _ _ T w Z
      obtain ⟨x, hx⟩ : ∃ x : B.LL, B.embLL x = Complex.exp (2 * Real.pi * Complex.I / B.toPre.restRowsFiniteGroupCard) :=
        hH.2 _ (Finset.mem_singleton_self _)
      refine ⟨x, ?_⟩
      show IsPrimitiveRoot x B.toPre.restRowsFiniteGroupCard
      rw [← IsPrimitiveRoot.map_iff_of_injective (f := B.embLL) B.embLL.injective, hx]
      exact Complex.isPrimitiveRoot_exp _ B.toPre.restRowsFiniteGroupCard_pos.ne'
  exact EvG.imp evG_good fun K _ _ _ _ _ => hLg K

end GlobalTheory.HeightCounting.Up
