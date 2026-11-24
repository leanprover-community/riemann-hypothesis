module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeBoundOfIsometricSphericalGL
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.LatHecke

theorem _root_.GlobalTheory.T.satake_bound_of_isometric_sphericalGL : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ρ : Representation ℂ (GL (Fin r) K) V) (v : V) (α : Multiset ℂ), α.card = r → (∀ g x, ‖ρ g x‖ = ‖x‖) → v ≠ 0 → (∀ g, glMap g (std O K r).1 = (std O K r).1 → ρ g v = v) → (∀ k ≤ r, ∀ s : Finset (GL (Fin r) K), Set.BijOn (fun g => glMap g (std O K r).1) s (Subtype.val '' subElem k (std O K r)) → ∑ g ∈ s, ρ g v = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v) → ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.LatHecke.satake_bound_of_isometric_spherical | exact GlobalTheory.LatHecke.satake_bound_of_isometric_spherical | (intros; apply GlobalTheory.LatHecke.satake_bound_of_isometric_spherical <;> assumption)
