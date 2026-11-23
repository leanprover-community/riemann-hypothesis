module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up

namespace DivLeviPf

section Euclid

variable {n p : ℕ} {g : Fin p → V n → ℂ} {y : V n}

theorem logSum_contDiffAt (hg : ∀ k, ContDiffAt ℂ ∞ (g k) y) (hne : ∃ k, g k y ≠ 0) :
    ContDiffAt ℝ ∞ (fun w => Real.log (∑ k, ‖g k w‖ ^ 2)) y := by
  have h1 : ContDiffAt ℝ ∞ (fun w => ∑ k, ‖g k w‖ ^ 2) y := by
    simp only [← Complex.normSq_eq_norm_sq]
    exact ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (hg k)
  exact h1.log (sum_normSq_pos hne).ne'

theorem logSum_levi_nonneg (hg : ∀ k, ContDiffAt ℂ ∞ (g k) y) (hne : ∃ k, g k y ≠ 0)
    (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun w => ((Real.log (∑ k, ‖g k w‖ ^ 2) : ℝ) : ℂ)) y ξ).re := by
  obtain ⟨k0, hk0⟩ := hne
  have h := leviLogNormSq n p g y ξ (fun k => (hg k).of_le HE.two_le_inf)
    (fun h => hk0 (congrFun h k0))
  have e : (fun w => ((Real.log (∑ k, ‖g k w‖ ^ 2) : ℝ) : ℂ)) =
      fun w => ((Real.log (sqNorm (fun i => g i w)) : ℝ) : ℂ) := by
    funext w
    simp only [← Complex.normSq_eq_norm_sq]
    rfl
  rw [e, h, Complex.ofReal_re]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

end Euclid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem contDiffAt_comp_cpt {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom)
    (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℂ ∞ (fun w => P (cpt X x0 w)) z := by
  have hc : Differentiable ℂ (cpt X x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
      (IW.cpt_entry_cd X x0 τ a b).differentiable (by simp)
  exact HE.contDiffAt_of_punct (ExF.isOpen_OmF X x0)
    (hP.comp hc.differentiableOn fun w hw => hw) hz

theorem exists_s_ne_zero {Xa : ArchInM X} (Fl : FlatM X Xa) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) :
    ∃ k, ∃ x ∈ X.dom, Fl.s k x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨j, -⟩ := (Fl.S_eq x0 hx0).1 fun k => h k x0 hx0
  have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
    show cpt X (Fl.xs j) 0 ∈ X.dom
    rw [IW.cpt_zero]
    exact Fl.xs_mem j
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [(ExF.isOpen_OmF X (Fl.xs j)).mem_nhds h0] with w hw
    ext k
    simp [h k _ hw]
  apply Fl.coord j
  rw [hev.fderiv_eq, fderiv_fun_const]
  have h2 := Xa.n_ge
  have : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  show LinearMap.det (0 : V (nd X) →ₗ[ℂ] V (nd X)) = 0
  exact LinearMap.det_zero' (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis

end DivLeviPf


end GlobalTheory.Up
