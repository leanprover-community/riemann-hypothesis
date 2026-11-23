module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBasisMem
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.HeightCont

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem height_continuousOn : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ W, ContinuousOn (fun x => d x W) {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)}) := by
  intro r X d hd W
  obtain ⟨w, hw, hΛ, hsp⟩ := GlobalTheory.LatBasis.exists_basis_mem r X W
  suffices H : ContinuousOn (fun x => d x (Submodule.span E (Set.range w)))
      {x : Frame X.Ψ r | (∀ τ : X.Ψ, (mat x τ).det ≠ 0)} by rwa [hsp] at H
  refine ContinuousOn.congr ?_ (fun x hx => hd x hx _ w hw hΛ)
  refine ContinuousOn.div_const ?_ _
  refine continuousOn_finsetProd _ fun τ _ x hx => ContinuousAt.continuousWithinAt ?_
  have hm : Continuous (fun x : Frame X.Ψ r => mat x τ) := continuous_apply τ
  have hr : ContinuousAt (Ring.inverse : ℂ → ℂ) (mat x τ).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (hx τ)
  have hi : ContinuousAt (fun x : Frame X.Ψ r => (mat x τ)⁻¹) x :=
    ContinuousAt.comp (f := fun x : Frame X.Ψ r => mat x τ) (continuousAt_matrix_inv _ hr)
      hm.continuousAt
  have hg : Continuous (fun A : Matrix (Fin r) (Fin r) ℂ =>
      ((A * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * (A * (Matrix.of fun k a => τ.1 (w a k)))).det.re) :=
    Complex.continuous_re.comp
      (((continuous_id.matrix_mul continuous_const).matrix_conjTranspose.matrix_mul
        (continuous_id.matrix_mul continuous_const)).matrix_det)
  exact ContinuousAt.comp (f := fun x : Frame X.Ψ r => (mat x τ)⁻¹) hg.continuousAt hi

end GlobalTheory.HeightCont
