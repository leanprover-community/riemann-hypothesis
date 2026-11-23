module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DomBy
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationRingCentreInChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

theorem _root_.GlobalTheory.T.valuation_ring_centre_in_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω Ω' : Type) [Field Ω] [Field Ω'] (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (i : Ω →+* Ω') (W : ValuationSubring Ω') (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k j, i (y ⟨k, j⟩ / y ⟨k, c k⟩) ∈ W) → ∃ q : Cpt ξ, InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c q ∧ DomBy W.toSubring i ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.exists_domBy_chart | exact GlobalTheory.CompanionTheory.Ar.OrVert.exists_domBy_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.exists_domBy_chart <;> assumption)
