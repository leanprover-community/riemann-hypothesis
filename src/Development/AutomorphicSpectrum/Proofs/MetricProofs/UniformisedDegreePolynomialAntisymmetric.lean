import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereSingularTotalMassDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPerInt

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem proportional_on_uniformised : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (U : Set X) (th : Ψ × Fin N → LocPot X) (ph : Ψ × Fin N → X → ℝ), j ≤ N → e = antisymDegree Ψ N → IsOpen U → IsNull A Uᶜ → (∀ p, IsPotential A (th p)) → (∀ p, A.SmoothOn U (ph p)) → IsUniformised A U j (fun p => th p + LocPot.ofFun (ph p)) → (∀ w : Fin e → Ψ × Fin N, MIntegrable A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) → ∃ v : ℝ, 0 < v ∧ toWt (formPoly e fun w => mInt A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) = C v * antisymDelta Ψ N :=
  @PositivityTheory.Xgp.t_per_int

end GlobalTheory.CompanionTheory.Ar.PB
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_potential_integral_formula : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (U : Set X) (th : Ψ × Fin N → LocPot X) (ph : Ψ × Fin N → X → ℝ), j ≤ N → e = antisymDegree Ψ N → IsOpen U → IsNull A Uᶜ → (∀ p, IsPotential A (th p)) → (∀ p, A.SmoothOn U (ph p)) → IsUniformised A U j (fun p => th p + LocPot.ofFun (ph p)) → (∀ w : Fin e → Ψ × Fin N, MIntegrable A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) → ∃ v : ℝ, 0 < v ∧ toWt (formPoly e fun w => mInt A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) = C v * antisymDelta Ψ N := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.proportional_on_uniformised
end

section
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem anSys_proportional : Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j D : ℕ) (S : AnSys D (Ψ × Fin N)), j ≤ N → D = antisymDegree Ψ N → IsUniformised S.A S.open' j S.potH → ∃ v : ℝ, 0 < v ∧ toWt S.degPoly = C v * antisymDelta Ψ N := by
  intro hI Ψ _ _ N j D S hj hD hU
  obtain ⟨hO, hNull, -, -, -⟩ := anSys_open_basics D (Ψ × Fin N) S
  have hInt := AnSys.mIntegrable_potH_and_mInt_eq_degNum hI.convergenceSigned D (Ψ × Fin N) S
  have hmain := GlobalTheory.T.uniformised_potential_integral_formula D S.X S.A Ψ N j S.open' S.th S.ph hj hD hO hNull
    (fun p => (S.sing p).1) (fun p => (S.sing p).2.1) hU (fun w => (hInt w).1)
  obtain ⟨v, hv, hEq⟩ := hmain
  refine ⟨v, hv, ?_⟩
  have hfun : (fun w : Fin D → Ψ × Fin N => mInt S.A (fun i => S.th (w i) + LocPot.ofFun (S.ph (w i))) (fun _ => 1)) = S.degNum :=
    funext fun w => (hInt w).2
  rw [hfun] at hEq
  exact hEq

end GlobalTheory.CompanionTheory.Ar.PB
end

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_degree_polynomial_antisymmetric : Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j D : ℕ) (S : AnSys D (Ψ × Fin N)), j ≤ N → D = antisymDegree Ψ N → IsUniformised S.A S.open' j S.potH → ∃ v : ℝ, 0 < v ∧ toWt S.degPoly = C v * antisymDelta Ψ N := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.anSys_proportional
end
