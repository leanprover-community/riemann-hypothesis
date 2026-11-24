module

public import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def zetaSubPole : ℂ → ℂ :=
  Function.update (fun s : ℂ => riemannZeta s - 1 / (s - 1)) 1 (Real.eulerMascheroniConstant : ℂ)

theorem zeta_sub_pole_differentiable : Differentiable ℂ zetaSubPole := by
  rw [← differentiableOn_univ,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs1 : s ≠ 1 := hs.2
    have hev : zetaSubPole =ᶠ[𝓝 s] fun z => riemannZeta z - 1 / (z - 1) := by
      filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
      exact Function.update_of_ne hz _ _
    have hd : DifferentiableAt ℂ (fun z => riemannZeta z - 1 / (z - 1)) s :=
      (differentiableAt_riemannZeta hs1).sub
        ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  · unfold zetaSubPole
    exact continuousAt_update_same.mpr tendsto_riemannZeta_sub_one_div

theorem zeta_minus_pole_eq {s : ℂ} (hs : s ≠ 1) : zetaSubPole s = riemannZeta s - 1 / (s - 1) := by
  unfold zetaSubPole
  exact Function.update_of_ne hs _ _

theorem dirichlet_product_entire : BqEntire := by
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h₁ h₂ hψ
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun s => DirichletCharacter.LFunction χ₁ s *
      DirichletCharacter.LFunction χ₂ s * DirichletCharacter.LFunction ψ s := ⟨_, rfl⟩
  have hPd : Differentiable ℂ P := by
    rw [hP]
    exact ((DirichletCharacter.differentiable_LFunction h₁).mul
      (DirichletCharacter.differentiable_LFunction h₂)).mul
      (DirichletCharacter.differentiable_LFunction hψ)
  have hds : Differentiable ℂ (dslope P 1) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hPd.differentiableOn
  refine ⟨fun s => zetaSubPole s * P s + dslope P 1 s,
    (zeta_sub_pole_differentiable.mul hPd).add hds, fun s hs => ?_⟩
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  show _ = zetaSubPole s * P s + dslope P 1 s + _
  rw [dslope_of_ne _ hs, slope_def_field, zeta_minus_pole_eq hs]
  simp only [Fbq, lamBq, hP]
  field_simp
  ring

end Formalism.ZeroFreeDirichlet
