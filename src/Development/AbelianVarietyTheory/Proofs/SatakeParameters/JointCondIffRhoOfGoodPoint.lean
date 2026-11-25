module

public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

noncomputable section

namespace GlobalTheory.ParamRepCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open scoped Pointwise

section Inertia

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
private lemma smul_mem_smul_valuationSubring_iff (h : _root_.Formalism.ConjugateSelfDual.G F Ω) (B : ValuationSubring Ω) (y : Ω) :
    h • y ∈ h • B ↔ y ∈ B := by
  refine ⟨fun hy => ?_, ValuationSubring.smul_mem_pointwise_smul h y B⟩
  have := ValuationSubring.smul_mem_pointwise_smul h⁻¹ _ _ hy
  simpa [smul_smul] using this

open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
private lemma valuation_smul_smul_lt_one_iff (h : _root_.Formalism.ConjugateSelfDual.G F Ω) (B : ValuationSubring Ω) (y : Ω) :
    (h • B).valuation (h • y) < 1 ↔ B.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', smul_mem_smul_valuationSubring_iff,
    ← smul_inv'', smul_mem_smul_valuationSubring_iff]
  simp


open Polynomial NumberField IsDedekindDomain in
open scoped Pointwise in
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] in
theorem _root_.GlobalTheory.ParamRepCompare.conj_mem_Ine_of_smul_eq {A A' : ValuationSubring Ω} {g σ : _root_.Formalism.ConjugateSelfDual.G F Ω}
    (hg : g • A = A') (hσ : σ ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A') : g⁻¹ * σ * g ∈ _root_.ReciprocityTheory.Gal.Ine (F := F) A := by
  subst hg
  obtain ⟨hdec, hval⟩ := hσ
  refine ⟨?_, fun x hx => ?_⟩
  · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hdec ⊢
    rw [mul_smul, mul_smul, hdec, inv_smul_smul]
  · rw [← valuation_smul_smul_lt_one_iff g]
    have hx' : (g • A).valuation (g • x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
      exact ValuationSubring.smul_mem_pointwise_smul g x A hx
    have := hval (g • x) hx'
    convert this using 2
    rw [smul_sub]
    simp [AlgEquiv.smul_def]

end Inertia

section Clauses

variable (D : D7)

end Clauses

end GlobalTheory.ParamRepCompare

end
