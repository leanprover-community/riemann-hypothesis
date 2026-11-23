module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 Polynomial
attribute [local instance] algMdl algPoly algRat

private theorem valCrit {R K : Type} [CommRing R] [Field K] (A : R →+* K) (x : K)
    (h : ∀ V : ValuationSubring K, (∀ r, A r ∈ V) → x ∈ V) : A.IsIntegralElem x := by
  letI := A.toAlgebra
  by_contra hx
  have hx' : x ∉ (integralClosure R K).toSubring := hx
  obtain ⟨V, hV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hx'
  exact hxV (h V fun r => hV ((integralClosure R K).algebraMap_mem r))

theorem UpperTheory.mem_ringOfIntegers_modularTowerTop_of_forall_valuation :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (f : topL X M), (∀ W : ValuationSubring X.K, X.OverY W → (f : X.K) ∈ W) → f ∈ FunctionField.ringOfIntegers Ω (topL X M) := by
  intro Ω _ _ ε X M f hf
  have key := valCrit ((topL X M).subtype.comp (algebraMap (Polynomial Ω) (topL X M))) (f : X.K) (by
    intro V hV
    apply hf V
    refine ⟨fun c => ?_, ?_⟩
    · have h1 := hV (Polynomial.C c)
      change ((jPoly X _ (Polynomial.C c) : X.K)) ∈ V at h1
      rwa [coe_jPoly, Polynomial.aeval_C] at h1
    · have h2 := hV Polynomial.X
      change ((jPoly X _ Polynomial.X : X.K)) ∈ V at h2
      rwa [coe_jPoly, Polynomial.aeval_X] at h2)
  exact RingHom.IsIntegralElem.of_map Subtype.val_injective key
