module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsUFD
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.WeierstrassPolynomialRing
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermGeneralCoordinates
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolGermsDomain
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

theorem coe_mkGerm {τ : Type} [Fintype τ] (f : (τ → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    ((mkGerm f hf : holGerms (0 : τ → ℂ)) : Germ (𝓝 (0 : τ → ℂ)) ℂ) = ↑f := rfl

theorem isUnit_mkGerm {τ : Type} [Fintype τ] (e : (τ → ℂ) → ℂ) (he : AnalyticAt ℂ e 0) (he0 : e 0 ≠ 0) :
    IsUnit (mkGerm e he) := by
  refine IsUnit.of_mul_eq_one (mkGerm (fun x => (e x)⁻¹) (he.inv he0)) (Subtype.ext ?_)
  show ((fun x => e x * (e x)⁻¹ : (τ → ℂ) → ℂ) : Germ (𝓝 (0 : τ → ℂ)) ℂ) =
    ((fun _ => (1 : ℂ) : (τ → ℂ) → ℂ) : Germ (𝓝 (0 : τ → ℂ)) ℂ)
  exact Germ.coe_eq.2 (by
    filter_upwards [he.continuousAt.eventually_ne he0] with x hx
    exact mul_inv_cancel₀ hx)

theorem uniqueFactorizationMonoid_holGerms_option (hN : AnalyticGermsNoetherian.Statement)
    (hG : GeneralLinearCoordinates.Statement) (hP : WeierstrassPreparation.Statement)
    (hD : WeierstrassDivision.Statement) (σ : Type) [Fintype σ]
    (hR : UniqueFactorizationMonoid (holGerms (0 : σ → ℂ))) :
    UniqueFactorizationMonoid (holGerms (0 : Option σ → ℂ)) := by
  have := hN (Option σ) 0
  have := hR
  refine { irreducible_iff_prime := fun {φ} => ⟨fun hφ => ?_, Prime.irreducible⟩ }
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have hnz : ¬ ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0 := fun h =>
    hφ.ne_zero (Subtype.ext (by rw [← hfφ]; exact Germ.coe_eq.2 h))
  obtain ⟨A, d, hAd⟩ := hG σ f hf hnz
  have hfA : AnalyticAt ℂ (f ∘ A) 0 := hf.comp_of_eq (A.analyticAt 0) (map_zero A)

  have hT : germAffineEquiv A (0 : Option σ → ℂ) φ = mkGerm (f ∘ A) hfA := by
    apply Subtype.ext
    show ((germPull (fun z : Option σ → ℂ => A z + 0) ((A.analyticAt 0).add analyticAt_const) (by simp) φ : holGerms (0 : Option σ → ℂ)) :
      Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = ↑(f ∘ A)
    rw [germPull_coe _ _ _ φ f hfφ]
    simp only [add_zero]
  refine (MulEquiv.prime_iff (germAffineEquiv A (0 : Option σ → ℂ))).1 ?_
  rw [hT]
  have hirrA : Irreducible (mkGerm (f ∘ A) hfA) := by
    rw [← hT]; exact (MulEquiv.irreducible_iff (germAffineEquiv A (0 : Option σ → ℂ))).2 hφ

  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hP σ d (f ∘ A) hfA hAd
  have hE := isUnit_mkGerm e he he0
  have hF : mkGerm (f ∘ A) hfA = polyToGerm σ (weierstrassPoly c hc) * mkGerm e he := by
    apply Subtype.ext
    rw [Subring.coe_mul, polyToGerm_weierstrassPoly, coe_mkGerm, coe_mkGerm, ← Germ.coe_mul]
    exact Germ.coe_eq.2 (by
      filter_upwards [hfe] with x hx
      rw [hx, Pi.mul_apply, mul_comm])
  have hassoc : Associated (polyToGerm σ (weierstrassPoly c hc)) (mkGerm (f ∘ A) hfA) :=
    ⟨hE.unit, by rw [hF, IsUnit.unit_spec]⟩
  have hirrW : Irreducible (polyToGerm σ (weierstrassPoly c hc)) := hassoc.irreducible_iff.2 hirrA
  refine hassoc.prime_iff.1 ?_

  have hprimeω : Prime (weierstrassPoly c hc) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.1 (weierstrassPoly_irreducible c hc hc0 hirrW)
  refine prime_map_of_prime (polyToGerm σ) hprimeω hirrW.ne_zero ?_
    (weierstrassPoly_dvd_of_polyToGerm_dvd c hc hc0)
  intro g
  obtain ⟨g₀, hg₀, hg₀g⟩ := g.2
  obtain ⟨q, a, hq, ha, hdiv⟩ := hD σ d (f ∘ A) g₀ hfA hg₀ hAd
  refine ⟨mkGerm (q * e) (hq.mul he), finPoly fun j => mkGerm (a j) (ha j), Subtype.ext ?_⟩
  rw [Subring.coe_add, Subring.coe_mul, polyToGerm_weierstrassPoly, polyToGerm_finPoly, coe_mkGerm, ← hg₀g,
    ← Germ.coe_mul, ← Germ.coe_add]
  exact Germ.coe_eq.2 (by
    filter_upwards [hdiv, hfe] with x hx hx'
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [hx, hx']
    ring)

theorem HolGermsUFD.proof (hP : WeierstrassPreparation.Statement) (hD : WeierstrassDivision.Statement) :
    HolGermsUFD.Statement := by
  have hG := GeneralLinearCoordinates.proof
  have hN := AnalyticGermsNoetherian.proof hD hG
  have hfin : ∀ n : ℕ, UniqueFactorizationMonoid (holGerms (0 : Fin n → ℂ)) := by
    intro n
    induction n with
    | zero =>
      let _ := isField_holGerms_fin_zero.toField
      infer_instance
    | succ n ih =>
      exact (germAffineEquiv (LinearEquiv.funCongrLeft ℂ ℂ (finSuccEquiv n)).toContinuousLinearEquiv
        (0 : Fin (n + 1) → ℂ)).symm.toMulEquiv.uniqueFactorizationMonoid
        (uniqueFactorizationMonoid_holGerms_option hN hG hP hD (Fin n) ih)
  intro σ _ w
  exact (germAffineEquiv (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv
    w).symm.toMulEquiv.uniqueFactorizationMonoid (hfin _)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
