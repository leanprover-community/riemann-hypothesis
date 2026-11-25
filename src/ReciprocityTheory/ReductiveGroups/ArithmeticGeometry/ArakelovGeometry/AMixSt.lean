module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChainA
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDefs

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Topology ContDiff

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem gaamix_cxHessian_comb {a b ψ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (s u : ℝ)
    (ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 a y') (hb : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 b y')
    (hψ : ψ =ᶠ[𝓝 y] fun y' => s * a y' + u * b y') :
    cxHessian ψ y = (s : ℂ) • cxHessian a y + (u : ℂ) • cxHessian b y := by
  have hd : fderiv ℝ ψ =ᶠ[𝓝 y] fun y' => s • fderiv ℝ a y' + u • fderiv ℝ b y' := by
    filter_upwards [hψ.eventuallyEq_nhds, ha, hb] with y' h1 h2 h3
    rw [h1.fderiv_eq]
    have d2 := h2.differentiableAt (by norm_num)
    have d3 := h3.differentiableAt (by norm_num)
    exact ((d2.hasFDerivAt.const_mul s).add (d3.hasFDerivAt.const_mul u)).fderiv
  have hH : fderiv ℝ (fderiv ℝ ψ) y =
      s • fderiv ℝ (fderiv ℝ a) y + u • fderiv ℝ (fderiv ℝ b) y := by
    rw [hd.fderiv_eq]
    have d2 := (ha.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have d3 := (hb.self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    exact ((d2.hasFDerivAt.const_smul s).add (d3.hasFDerivAt.const_smul u)).fderiv
  ext i j
  simp only [cxHessian, hH, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.smul_apply]
  push_cast
  ring

theorem gaamix_ne_zero_of_mcPts {P : Ideal (MRing (GlobalTheory κ))} {z : Ix κ → ℂ} (hz : z ∈ mcPts P) :
    z ≠ 0 := by
  obtain ⟨i, hi⟩ := hz.1 ()
  rintro rfl
  exact hi rfl

theorem gbamix_ne_zero_of_blocks {z : Ix κ → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : z ≠ 0 := by
  obtain ⟨i, hi⟩ := hz ()
  rintro rfl
  exact hi rfl

theorem gbamix_smoothHerm_ofCone {m : ConeMetric (C := ℂ) (ι := Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  exact (show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m.ρ {z | z ≠ 0} from hm).mono
    fun z hz => gbamix_ne_zero_of_blocks hz

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
