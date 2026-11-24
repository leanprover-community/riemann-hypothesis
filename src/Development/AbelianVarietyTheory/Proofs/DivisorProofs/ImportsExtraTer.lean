module

public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.LiftAndFactorization

open Formalism.L2.Pj

theorem exists_lift (T : CDVR) (x : T.Fr) (hx : x ≠ 0 → vV T.V x = 0) :
    ∃ b : T.V, algebraMap T.V T.Fr b = x := by
  by_cases h0 : x = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  have hne : (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x ≠ 0 :=
    (Valuation.ne_zero_iff _).2 h0
  have hlog : WithZero.log ((IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr x) = 0 := by
    have := hx h0
    unfold vV valV at this
    exact neg_eq_zero.1 this
  have := WithZero.exp_log hne
  rw [hlog, WithZero.exp_zero] at this
  exact this.ge

theorem exists_factor (T : CDVR) {F : Type} [Field F] (io : F →+* T.Fr)
    (h : ∀ a : F, a ≠ 0 → vV T.V (io a) = 0) :
    ∃ φ : F →+* T.V, (algebraMap T.V T.Fr).comp φ = io := by
  have key : ∀ a : F, ∃ b : T.V, algebraMap T.V T.Fr b = io a := fun a =>
    exists_lift T (io a) (fun ha => h a (fun h0 => ha (by rw [h0, map_zero])))
  choose f hf using key
  have inj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  refine ⟨{ toFun := f
            map_one' := inj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => inj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := inj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => inj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _)]) }, ?_⟩
  ext a
  exact hf a

end GlobalTheory.LiftAndFactorization
