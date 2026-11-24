module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubringCoordsComplexValue
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

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.subring_coords_complex_value : ∀ (X : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (W : Subring Ω') (φ : W →+* ℂ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordsAt ξ y z w → (∀ a : W, φ a ≠ 0 → IsUnit a) → (∀ (k : K) (c e : J k), w ⟨k, c⟩ ≠ 0 → ∃ h : i (y ⟨k, e⟩ / y ⟨k, c⟩) ∈ W, φ ⟨_, h⟩ * w ⟨k, c⟩ = w ⟨k, e⟩) → ∀ (a : Ω) (r : ℂ), ValAt ξ z a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RegVal.contains_localRing | exact GlobalTheory.CompanionTheory.Ar.RegVal.contains_localRing | (intros; apply GlobalTheory.CompanionTheory.Ar.RegVal.contains_localRing <;> assumption)
