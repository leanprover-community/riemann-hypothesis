module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesIdentityTermDominates
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.poincareSeries_pairing_ne_zero_of_large_level : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S') (M : DSModel V S) (p : Pack M₀ M) (Q : ℝ), p.Base d → ∀ (Λ : Lat Y) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC Y Λ → 𝔪 ≠ ⊥ → ∀ (v : GlobalTheory.Unf.Vol Y) (φ : GA D Y → ℂ) (c : ℂ) (b s : ℝ) (x : GA D Y), GlobalTheory.Unf.IsContAut Y φ → (∀ h, ‖φ h‖ ≤ b) → b / 2 < ‖φ x‖ → 0 ≤ s → s ≤ 1 → Long θ p.A Λ x s → p.AdelicAt θ d Q (d.lat Λ fun _ => 1) 𝔪 v.μ φ c → 2 * Real.exp (Q + (6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) ≤ s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → 1 < s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm 𝔪) → ∫ h in v.𝓕, poin θ M (congLev D.sp.cm V.gram (d.lat Λ fun _ => 1) 𝔪) (p.v θ) (stabilizerEmbedding d x⁻¹) (p.v θ) (stabilizerEmbedding d h) * φ h ∂v.μ ≠ 0 := by
  first | exact @GlobalTheory.IdDom.identity_dominates | exact GlobalTheory.IdDom.identity_dominates | (intros; apply GlobalTheory.IdDom.identity_dominates <;> assumption)
