module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataDescentNumberField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_cmArcData_descent_numberField : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (σ₁ : K →+* ℂ) (σ : c.F →+* ℂ) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (φ : aC.D₀.P.A.left ⟶ B.pol.A.left) (n : ℕ), letI := H.starRing; σ₁.comp (algebraMap c.F K) = σ → 0 < n → IsPolFibre (σ₁.comp (algebraMap (𝓞 K) K)) B.pol aC.D₀.P φ → (∀ x, (aC.oa.onB.act x).left ≫ φ = φ ≫ (B.t.act.act x).left) → TauCan aC.D₀ n → ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (_ : Algebra c.F K₂) (i : K →ₐ[c.F] K₂) (σ₂ : K₂ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₂ (algebraMap c.F K₂)) (p : Out.IsPullDeg σ₂ a.D₀ aC.D₀) (ψ : a.D₀.P.A.left ⟶ B.pol.A.left), σ₂.comp (i : K →+* K₂) = σ₁ ∧ InBC σ₂ a aC p ∧ TauCan a.D₀ n ∧ IsPolFibre ((i : K →+* K₂).comp (algebraMap (𝓞 K) K)) B.pol a.D₀.P ψ ∧ ∀ x, (a.oa.onB.act x).left ≫ ψ = ψ ≫ (B.t.act.act x).left := by
  first | exact @GlobalTheory.ArcCM.exists_arcIn_numberField | exact GlobalTheory.ArcCM.exists_arcIn_numberField | (intros; apply GlobalTheory.ArcCM.exists_arcIn_numberField <;> assumption)
