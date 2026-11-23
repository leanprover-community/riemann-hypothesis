module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

theorem glue : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ f : ∀ k, Hol (K.W k), (∀ k k' (h : K.le 0 k' k), Charts.sh h (f k) = f k') → ∃ G : Tot I g → ℂ, AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, (f k).fn p = G p) ∧ (∀ (l : Λ) (q : Hol F.V), (∀ k k' (h : K.le l k' k), Charts.sh h (f k) = f k' + K.cst k' q) → ∀ p : Tot I g, p.1 ∈ F.V → G (F.shift l p) = G p + q.fn p.1) ∧ ((∀ k a, dw a (f k) = 0) → ∀ z ∈ F.V, ∀ w, G (z, w) = G (z, 0)) := by
  intro I _ g Λ _ F K hK f hf
  classical
  have indep : ∀ k₁ k₂ p, p ∈ K.W k₁ → p ∈ K.W k₂ → (f k₁).fn p = (f k₂).fn p := by
    intro k₁ k₂ p h₁ h₂
    obtain ⟨k, hk, hl₁, hl₂⟩ := hK.2 0 k₁ k₂ p h₁ (by rw [F.shift_zero]; exact h₂)
    have e₁ := Charts.fn_sh hl₁ (f k₁) hk
    have e₂ := Charts.fn_sh hl₂ (f k₂) hk
    rw [hf k₁ k hl₁, F.shift_zero] at e₁
    rw [hf k₂ k hl₂, F.shift_zero] at e₂
    rw [← e₁, ← e₂]
  let G : Tot I g → ℂ := fun p ↦ if h : ∃ k, p ∈ K.W k then (f h.choose).fn p else 0
  have hG : ∀ k, ∀ p ∈ K.W k, (f k).fn p = G p := by
    intro k p hp
    have h : ∃ k, p ∈ K.W k := ⟨k, hp⟩
    simp only [G, dif_pos h]
    exact indep _ _ _ hp h.choose_spec
  have hGev : ∀ k, ∀ p ∈ K.W k, G =ᶠ[𝓝 p] (f k).fn := fun k p hp ↦ by
    filter_upwards [(K.W k).isOpen.mem_nhds hp] with q hq using (hG k q hq).symm
  refine ⟨G, ?_, hG, ?_, ?_⟩
  · intro p hp
    obtain ⟨k, hk⟩ := hK.1 p hp
    exact ((f k).analytic p hk).congr (hGev k p hk).symm
  · intro l q hq p hp
    obtain ⟨k₁, h₁⟩ := hK.1 p hp
    obtain ⟨k₂, h₂⟩ := hK.1 (F.shift l p) hp
    obtain ⟨k, hk, -, hl⟩ := hK.2 l k₁ k₂ p h₁ h₂
    have e := congrArg (fun u ↦ Hol.fn u p) (hq k₂ k hl)
    rw [Charts.fn_sh hl _ hk, Hol.fn_add _ _ hk, Charts.fn_cst K k q hk] at e
    rw [← hG k₂ _ h₂, ← hG k p hk, e]
  · intro h0 z hz w
    have hder : ∀ w' : Fin g → ℂ, HasFDerivAt (fun u ↦ G (z, u)) (0 : (Fin g → ℂ) →L[ℂ] ℂ) w' := by
      intro w'
      obtain ⟨k, hk⟩ := hK.1 (z, w') hz
      have hfd : HasFDerivAt (fun u : Fin g → ℂ ↦ ((z, u) : Tot I g))
          (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ)) w' :=
        (hasFDerivAt_const z w').prodMk (hasFDerivAt_id w')
      have hGd : HasFDerivAt G (fderiv ℂ (f k).fn (z, w')) (z, w') := by
        rw [← (hGev k _ hk).fderiv_eq]
        exact (((f k).analytic _ hk).differentiableAt.congr_of_eventuallyEq (hGev k _ hk)).hasFDerivAt
      have hL : (fderiv ℂ (f k).fn (z, w')).comp (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ)) = 0 := by
        have hs : ∀ a : Fin g, fderiv ℂ (f k).fn (z, w') ((0, Pi.single a 1) : Tot I g) = 0 := by
          intro a
          have := Hol.fn_der ((0, Pi.single a 1) : Tot I g) (f k) hk
          rw [show Hol.der _ (f k) = dw a (f k) from rfl, h0 k a, ← Hol.ev_apply _ hk, map_zero] at this
          exact this.symm
        refine ContinuousLinearMap.ext fun v ↦ ?_

        rw [← Finset.univ_sum_single v, map_sum, ContinuousLinearMap.zero_apply]
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        have e : Pi.single a (v a) = v a • (Pi.single a 1 : Fin g → ℂ) := by
          rw [← Pi.single_smul]; simp
        rw [e, map_smul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hs a, smul_zero]
      have := hGd.comp w' hfd
      rw [hL] at this
      exact this
    exact is_const_of_fderiv_eq_zero (fun w' ↦ (hder w').differentiableAt) (fun w' ↦ (hder w').fderiv) w 0

end GlobalTheory.AnPer.Charts
