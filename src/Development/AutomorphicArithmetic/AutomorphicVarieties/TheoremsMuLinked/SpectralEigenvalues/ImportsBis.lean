module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreFurther
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

open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.ell :
    ∀ (O Λ Γ X : Type) [CommRing O] [CommRing Λ] [Algebra O Λ] [CommGroup Γ] [AddCommGroup X] [Module O X] (th₀ : Λ →ₐ[O] O) (d : Λ →ₗ[O] X) (χ : Γ →* Multiplicative X), (∀ a b, d (a * b) = th₀ a • d b + th₀ b • d a) → ∃ (th : MonoidAlgebra Λ Γ →ₐ[O] O) (ell : MonoidAlgebra Λ Γ →ₗ[O] X), (∀ g a, th (MonoidAlgebra.single g a) = th₀ a) ∧ (∀ a b, ell (a * b) = th a • ell b + th b • ell a) ∧ ∀ g a, ell (MonoidAlgebra.single g a) = d a + th₀ a • Multiplicative.toAdd (χ g) :=
  _root_.UpperTheory.Reformulated.B.Qh12.ell
