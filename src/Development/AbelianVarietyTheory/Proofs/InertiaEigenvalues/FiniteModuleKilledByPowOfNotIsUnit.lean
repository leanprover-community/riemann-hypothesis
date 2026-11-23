module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Basic.Finite.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import ReciprocityTheory.BasicDefinitions.AdRep
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory

theorem finite_module_killed_by_pow_of_not_isUnit :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (lam : O), ¬ IsUnit lam →
    ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], ∃ a : ℕ, ∀ x : X, lam ^ a • x = 0 := by
  intro O _ _ lam hlam X _ _ _
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes (R := O) X lam
  set Y : Submodule O X := LinearMap.range (lam ^ n • (LinearMap.id : X →ₗ[O] X)) with hY
  have hFG : Y.FG := Module.Finite.iff_fg.mp inferInstance
  have hle : Y ≤ Ideal.span {lam} • Y := by
    intro y hy
    have hy' : y ∈ LinearMap.range (lam ^ (n + 1) • (LinearMap.id : X →ₗ[O] X)) := by
      rw [← hn (n + 1) (Nat.le_succ n)]; exact hy
    obtain ⟨x, rfl⟩ := hy'
    have hmem : lam ^ n • x ∈ Y := ⟨x, by simp⟩
    have : (lam ^ (n + 1) • (LinearMap.id : X →ₗ[O] X)) x = lam • (lam ^ n • x) := by
      simp [pow_succ', mul_smul]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self lam) hmem
  have hjac : Ideal.span {lam} ≤ (⊥ : Ideal O).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal lam).mpr hlam
  have hbot : Y = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ Y hFG hle hjac
  refine ⟨n, fun x => ?_⟩
  have : lam ^ n • x ∈ Y := ⟨x, by simp⟩
  rw [hbot] at this
  simpa using this

end GlobalTheory
