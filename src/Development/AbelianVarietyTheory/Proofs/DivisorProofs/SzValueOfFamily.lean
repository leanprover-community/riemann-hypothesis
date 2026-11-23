module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOpsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastOfForallRatGtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicOfRationalValuationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegrallyClosedPadicIntegralSubringStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionValuationBoundRingClosureStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem sz_value_of_family (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (r : ℝ) (τ₀ : ℍ) (Ω : ℂ)
    (hN : 0 < N) (hact : ActBij act) (hf : IsFam act w f) (hq : ∀ i, QAll (Sz l lam r) N (f i))
    (hj : Sz l lam 0 (jT τ₀)) (hΩ : Ω ^ 12 = DD τ₀) (i : ι) :
    Sz l lam r (f i τ₀ / Ω ^ w) := by
  refine GlobalTheory.T.algebraicValuationAtLeast_of_forall_rat_gt l lam r _ fun q hrq => ?_
  obtain ⟨c, hc0, hc, hc'⟩ := GlobalTheory.T.exists_algebraic_of_rational_valuation l lam q
  obtain ⟨R, hR, hcl⟩ := GlobalTheory.T.exists_integrallyClosed_padicIntegralSubring l lam
  obtain ⟨hconst, hmono, -, hmul, -⟩ := GlobalTheory.T.qExpansionValuationBound_ring_closure l lam N hN
  have hfam : IsFam act w fun i τ => c * f i τ := (GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act).2.2.1 w c f hf
  have hq' : ∀ i, QAll (· ∈ R) N fun τ => c * f i τ := fun i => by
    obtain ⟨a, ha, ha'⟩ := hmono _ 0 _ (by linarith) (hmul _ _ _ _ (hconst _ c hc) (hq i))
    exact ⟨a, ha, fun n => (hR _).2 (ha' n)⟩
  have hjR : IsIntegral R (jT τ₀) :=
    isIntegral_algebraMap (R := R) (A := ℂ) (x := ⟨jT τ₀, (hR _).2 hj⟩)
  have h0 : Sz l lam 0 (c * f i τ₀ / Ω ^ w) :=
    (hR _).1 (hcl _ (GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act w N _ R τ₀ Ω hN hact hfam hq' hjR hΩ i))
  have h1 := (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.1 _ _ _ _ hc' h0
  have e : c⁻¹ * (c * f i τ₀ / Ω ^ w) = f i τ₀ / Ω ^ w := by
    rw [mul_div_assoc, inv_mul_cancel_left₀ hc0]
  rwa [add_zero, e] at h1

end GlobalTheory.QFam
