module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualDataTransvectionPrincipalLevel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_selfDual_data_transvection_principal_level : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ k : (U σ).Comp, ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (U σ).X k ∧ Xx.g = l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ (∀ γ ∈ Xx.Γ, ∀ v ∈ Xx.L', (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v ∈ Xx.L') ∧ ∃ M : ℝ, 0 < M ∧ M * Xx.k0 = 2 * l.M * Real.sqrt D.host.d ∧ ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = Xx.flowMat v τ ((M : ℂ) * τ.1 b) := by
  first | exact @GlobalTheory.LevGeo.exists_dataX_transv | exact GlobalTheory.LevGeo.exists_dataX_transv | (intros; apply GlobalTheory.LevGeo.exists_dataX_transv <;> assumption)
