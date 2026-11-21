import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology

variable {J : Type} [Fintype J] {D : ℕ}









theorem adens_maDensity_eq_maDens (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    maDensity φ z = ReciprocityTheory.AnForm.maDens φ z := rfl



theorem adens_contDiffAt_logρ {m : ConeMetric ℂ J} (hsm : IsSmoothMetric m) {γ' : (Fin D → ℂ) → J → ℂ}
    {v : Fin D → ℂ} (hγ' : AnalyticAt ℂ γ' v) (hne : γ' v ≠ 0) :
    ContDiffAt ℝ 2 (fun w => Real.log (m.ρ (γ' w))) v := by
  have hρ' : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) m.ρ {z | z ≠ 0} := contDiffOn_infty.1 hsm 2
  have hρ : ContDiffAt ℝ 2 m.ρ (γ' v) := hρ'.contDiffAt (isOpen_ne.mem_nhds hne)
  have hγ : ContDiffAt ℝ 2 γ' v := (hγ'.contDiffAt).restrict_scalars ℝ
  exact (hρ.comp v hγ).log (m.pos _ hne).ne'


end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
