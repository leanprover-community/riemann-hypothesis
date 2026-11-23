module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaLevelDataFormsSystemStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSeriesSpanBoundedFormsStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem GlobalTheory.SW.level_theta_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ μ : GL (Fin r) E → Lt E r → ℂ, (∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (F : Lt E r → Frame X.Ψ r → ℂ), IsForm X D.grp D.lats μ (wtOf X hr c c' n) F → InSpan X hr bas idx M D.lats (D.phi bas hn v₀) (Harm.rowHighest ℂ c c' : Submodule ℂ (Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))) F := by
  intro E _ _ _ r X g q0 hr bas idx n hS hE hn4 D hn M hM hMD v₀ hv μ hμ c c' F hF

  have hd : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hr1 : r ≤ Module.finrank ℚ E * r := Nat.le_mul_of_pos_left r hd
  have h4 : 4 * r < n := by
    generalize Module.finrank ℚ E * r = k at hr1 hn4
    omega

  exact GlobalTheory.T.hermitianTheta_series_span_bounded_forms E r X g q0 hr bas idx n hS hE h4 M D.grp D.lats (D.phi bas hn v₀) μ hM
    (GlobalTheory.T.hermitianThetaLevelData_forms_system E r X g bas idx n hS hE hn4 D hn M hM hMD v₀ hv μ hμ) c c' F hF
