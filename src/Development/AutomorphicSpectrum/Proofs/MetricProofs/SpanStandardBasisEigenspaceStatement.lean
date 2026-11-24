module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BigZe
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SpanStandardBasisEigenspace
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
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem _root_.GlobalTheory.T.span_standard_basis_eigenspace : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ τ, Submodule.span ℂ (Set.range fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = eigSp B (σ τ) ∧ Submodule.span ℂ (Set.range fun i : Fin j => (Pi.single (e (Sum.inr i, τ)) 1 : Fin g → ℂ)) = eigSp B ((starRingEnd ℂ).comp (σ τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames.span_single_eigSp | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames.span_single_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.Frames.span_single_eigSp <;> assumption)
