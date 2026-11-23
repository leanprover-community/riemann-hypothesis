module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CuspFlowEqTorusAction
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

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

theorem _root_.GlobalTheory.T.cuspFlow_eq_torusAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ η : Fin ρ → E, (∑ a, η a • cu.e a) ∈ X.Λ → ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ), (∀ s x, X.flow (∑ a, η a • cu.e a) (fun τ => (s τ : ℂ)) x = zAct X cu (L s) x) ∧ (∀ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ → ∀ s, ∑ k, phZ X cu χ k * L s k = 2 * ∑ τ : X.Ψ, (τ.1 (hq χ η)).re * s τ) ∧ ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  first | exact @GlobalTheory.CuspFlow.flow_eq_zAct | exact GlobalTheory.CuspFlow.flow_eq_zAct | (intros; apply GlobalTheory.CuspFlow.flow_eq_zAct <;> assumption)
