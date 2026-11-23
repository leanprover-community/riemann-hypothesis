module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRepresentationSpectralProjectors
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.lie_representation_spectral_projectors : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ), b.IsType σ ρ → ∃ E : Fin D.a → Matrix (Fin D.g) (Fin D.g) ℂ, (∀ i, E i * E i = E i) ∧ (∀ i, (E i).trace = (D.m : ℂ)) ∧ (∀ i c, ρ (algebraMap (𝓞 D.F) D.O c) * E i = σ (b.t i c) • E i) ∧ (∀ i c, E i * ρ (algebraMap (𝓞 D.F) D.O c) = σ (b.t i c) • E i) ∧ (2 * σ b.ρ - D.tr) • ∑ i, E i = ρ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : ℂ) - σ b.ρ) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) := by
  first | exact @GlobalTheory.UPel.HT.LieProj.lie_projectors | exact GlobalTheory.UPel.HT.LieProj.lie_projectors | (intros; apply GlobalTheory.UPel.HT.LieProj.lie_projectors <;> assumption)
