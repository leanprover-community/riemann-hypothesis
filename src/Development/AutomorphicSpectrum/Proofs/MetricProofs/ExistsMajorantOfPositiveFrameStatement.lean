module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMajorantOfPositiveFrame
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.exists_majorant_of_positive_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (Pt τ).PosDef) → (∀ τ, Pt τ * (C.gr τ)⁻¹ * Pt τ = C.gr τ) → ∃ M : Majorant C.h (Pi.basisFun E (Fin (j + j'))), (∀ (a : C.Arch) (x : Λ), M.len (invApply a (vecAt (Pi.basisFun E (Fin (j + j'))) (C.e x))) ^ 2 = ∑ τ, (star (C.tm a⁻¹ τ *ᵥ C.vec x τ) ⬝ᵥ (Pt τ *ᵥ (C.tm a⁻¹ τ *ᵥ C.vec x τ))).re) ∧ ∀ c : C.Arch, c ∈ M.stab ↔ ∀ τ, (C.tm c τ)ᴴ * Pt τ * C.tm c τ = Pt τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj.exists_majorant | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj.exists_majorant | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TauMaj.exists_majorant <;> assumption)
