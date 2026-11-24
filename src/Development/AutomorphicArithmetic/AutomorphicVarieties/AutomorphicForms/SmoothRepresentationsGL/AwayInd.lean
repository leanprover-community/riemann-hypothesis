module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem fin_bad {E : Type} [Field E] [NumberField E] {n : ℕ} (k : GL (Fin n) (Af E)) :
    {w | cmp w k ∉ GlobalTheory.LFun.KGL w (n := n)}.Finite := by
  have h : ∀ x : Af E, ∀ᶠ w in Filter.cofinite, pLoc E w x ∈ Formalism.UG.Ov E w := fun x => x.2
  have h1 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w (k.val i j) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in Filter.cofinite, ∀ i j, pLoc E w ((k⁻¹).val i j) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h3 : ∀ᶠ w in Filter.cofinite, cmp w k ∈ GlobalTheory.LFun.KGL w (n := n) := by
    filter_upwards [h1, h2] with w a b
    rw [GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv]
    exact ⟨a, b⟩
  exact h3

theorem UpperTheory.V.Af.Smo.awayInd :
    UpperTheory.V.Af.Smo.AwayInd := by
  intro E _ _ n S P h0 h1
  classical
  suffices H : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), ∀ k, Away S k → (∀ w ∉ T, cmp w k ∈ GlobalTheory.LFun.KGL w (n := n)) → P k by
    intro k hk
    refine H (fin_bad k).toFinset k hk fun w hw => ?_
    by_contra h
    exact hw ((Set.Finite.mem_toFinset _).2 h)
  intro T
  induction T using Finset.induction_on with
  | empty => exact fun k hk h => h0 k ⟨hk, fun w => h w (Finset.notMem_empty w)⟩
  | insert w T hw ih =>
    intro k hk h
    by_cases hS : w ∈ S
    · refine ih k hk fun v hv => ?_
      by_cases e : v = w
      · subst e; rw [hk v hS]; exact one_mem _
      · exact h v (by simp [e, hv])
    · have e1 : cmp w (k * (locGL E n w (cmp w k))⁻¹) = 1 := by
        rw [map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL, mul_inv_cancel]
      have e2 : ∀ v, v ≠ w → cmp v (k * (locGL E n w (cmp w k))⁻¹) = cmp v k := fun v e => by
        rw [map_mul, map_inv, GlobalTheory.CuspRep.pLoc_locGL_of_ne e, inv_one, mul_one]
      have a : Away S (k * (locGL E n w (cmp w k))⁻¹) := fun v hv => by
        rw [e2 v (fun e => hS (e ▸ hv)), hk v hv]
      have p := ih _ a fun v hv => by
        by_cases e : v = w
        · subst e; rw [e1]; exact one_mem _
        · rw [e2 v e]; exact h v (by simp [e, hv])
      have q := h1 w hS _ a e1 p (cmp w k)
      rwa [inv_mul_cancel_right] at q
