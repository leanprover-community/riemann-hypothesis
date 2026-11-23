module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemBasicOpenOfMemBasicOpenNormCoeffStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSecNormCoeffLocalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemBasicOpenNormCoeffOfFibreStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.NormalDescent

theorem exists_sec_image {X Y : Scheme.{0}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {M : LB X} (hM : M.IsLB) (t : (M.pull f).Sec) : ∃ u : ∀ k, (lbPow M k).Sec,
      (∀ x : X, (∀ y : Y, f y = x → y ∈ nonzeroLocus t) → ∃ k, 1 ≤ k ∧ x ∈ nonzeroLocus (u k)) ∧
      ∀ (x : X) (k : ℕ), 1 ≤ k → x ∈ nonzeroLocus (u k) → ∃ y ∈ nonzeroLocus t, f y = x := by
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_sec_normCoeff_local' f hM t
  refine ⟨u, fun x hx => ?_, fun x k hk hx => ?_⟩
  · obtain ⟨V, hV, _, _, τ, hxV, ht, hc⟩ := hu x
    obtain ⟨k, hk, h⟩ := GlobalTheory.T.exists_mem_basicOpen_normCoeff_of_fibre f hV τ x hxV fun y hy => (ht y (hy ▸ hxV)).1 (hx y hy)
    exact ⟨k, hk, (hc k x hxV).2 h⟩
  · obtain ⟨V, hV, _, _, τ, hxV, ht, hc⟩ := hu x
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.T.exists_mem_basicOpen_of_mem_basicOpen_normCoeff' f hV τ x k hxV hk ((hc k x hxV).1 hx)
    exact ⟨y, (ht y hxV).2 hy, rfl⟩

theorem isAmpleLB_of_pull : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X), AlgebraicGeometry.IsNoetherian X →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsFinite f → Function.Surjective f →
    ∀ L : ReciprocityTheory.ChartRestriction.G.Semi.LB X, L.IsLB → GlobalTheory.IsAmpleLB (L.pull f) → GlobalTheory.IsAmpleLB L := by
  intro X X' f _ hN _ hs L hL h
  have := GlobalTheory.IsNormalScheme.of_pred hN
  have : Surjective f := ⟨hs⟩
  refine GlobalTheory.isAmpleLB_of_forall_le hL fun x U hx => ?_
  have hfin : (f ⁻¹' {x}).Finite := f.finite_preimage_singleton x
  obtain ⟨n, hn, s, hS, hle, -⟩ := h.exists_affine_finite_subset hfin (U := f ⁻¹ᵁ U)
    (fun y (hy : f y = x) => show f y ∈ U from hy ▸ hx)
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL n) f) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL f n).symm s
  obtain ⟨u, hu₁, hu₂⟩ := exists_sec_image f (isLB_lbPow hL n) t
  obtain ⟨k, hk, hxk⟩ := hu₁ x fun y hy => ht.ge (hS hy)
  have e := nonzeroLocus_secOfPowPow (u k)
  refine ⟨n * k, Nat.mul_pos hn hk, secOfPowPow (u k), e.ge hxk, fun z hz => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hu₂ z k hk (e.le hz)
  exact hle (ht.le hw)

end GlobalTheory.NormalDescent
