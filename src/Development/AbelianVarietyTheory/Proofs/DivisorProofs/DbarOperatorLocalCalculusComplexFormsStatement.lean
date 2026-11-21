import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLeibnizOfCommute
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex

section
set_option autoImplicit false

open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm

namespace GlobalTheory.CxForm

theorem dbarAt_local_calculus : ∀ (n : ℕ) (v : V n),
    (∀ α β : V n → Alt n, α =ᶠ[𝓝 v] β → dbarAt α v = dbarAt β v) ∧
    (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n),
      (∀ j ∈ s, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α j x) S) v) →
      dbarAt (fun x => ∑ j ∈ s, α j x) v = ∑ j ∈ s, dbarAt (α j) v) ∧
    (∀ (c : ℂ) (α : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) →
      dbarAt (fun x => c • α x) v = c • dbarAt α v) ∧
    (∀ γ : Alt n, dbarAt (fun _ => γ) v = 0) ∧
    (∀ (w : V n → Ev n) (β : V n → Alt n),
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr ((w x : Alt n)) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (β x) S) v) →
      dbarAt (fun x => (w x : Alt n) * β x) v =
        dbarAt (fun x => (w x : Alt n)) v * β v + (w v : Alt n) * dbarAt β v) := by
  intro n v
  obtain ⟨-, hsmul, hsum, hgerm, hconst⟩ := GlobalTheory.CxForm.delAt_dbarAt_linear_local n v
  exact ⟨fun α β h => (hgerm α β h).2, fun J s α h => (hsum J s α h).2, fun c α h => (hsmul α c h).2,
    fun γ => (hconst γ).2, fun w β hw hβ =>
      (FormMul.leibniz_of_comm n (fun x => (w x : Alt n)) β v (w v : Alt n) hw hβ).2
        fun a => Subalgebra.mem_center_iff.1 (w v).2 (dzb a)⟩

end GlobalTheory.CxForm
end

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_operator_local_calculus_complex_forms : ∀ (n : ℕ) (v : V n), (∀ α β : V n → Alt n, α =ᶠ[𝓝 v] β → dbarAt α v = dbarAt β v) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α j x) S) v) → dbarAt (fun x => ∑ j ∈ s, α j x) v = ∑ j ∈ s, dbarAt (α j) v) ∧ (∀ (c : ℂ) (α : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v) → dbarAt (fun x => c • α x) v = c • dbarAt α v) ∧ (∀ γ : Alt n, dbarAt (fun _ => γ) v = 0) ∧ (∀ (w : V n → Ev n) (β : V n → Alt n), (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr ((w x : Alt n)) S) v) → (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (β x) S) v) → dbarAt (fun x => (w x : Alt n) * β x) v = dbarAt (fun x => (w x : Alt n)) v * β v + (w v : Alt n) * dbarAt β v) := by
  atlas_forward_decl GlobalTheory.CxForm.dbarAt_local_calculus
end
