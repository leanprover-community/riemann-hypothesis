module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspMemCuspFormsOfKilledCoefZero
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

theorem _root_.GlobalTheory.T.maxCusp_mem_cuspForms_of_killedCoef_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), (∀ ξ, X.IsIso ξ → ∃ cu : CuspFD X ρ, ξ ∈ Submodule.span E (Set.range cu.e)) → (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) → ∀ (la : Wt X.Ψ r), (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) → ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SS la → (∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c → ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0) → P ∈ X.SSgt la c := by
  first | exact @GlobalTheory.maxCusps_mem_SSgt_of_coef_eq_zero | exact GlobalTheory.maxCusps_mem_SSgt_of_coef_eq_zero | (intros; apply GlobalTheory.maxCusps_mem_SSgt_of_coef_eq_zero <;> assumption)
