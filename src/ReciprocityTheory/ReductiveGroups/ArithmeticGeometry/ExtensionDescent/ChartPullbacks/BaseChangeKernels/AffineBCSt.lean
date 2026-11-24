module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

def AffineBCSt : Prop :=
  ∀ {G B G' B' : Scheme.{0}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B} {b : B' ⟶ B},
    IsPullback g q' q b → IsAffineHom q → ∀ {X : Type} [AddCommMonoid X]
    {V : B.Opens}, IsAffineOpen V → ∀ {V' : B'.Opens}, IsAffineOpen V' →
    V' ≤ b ⁻¹ᵁ V → ∀ (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V))
    (φ : Multiplicative X →* Γ(G, q ⁻¹ᵁ V)) (φ' : Multiplicative X →* Γ(G', q' ⁻¹ᵁ V')),
    (∀ x, φ' x = g.appLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG (φ x)) →
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.app V).hom φ (fun _ _ => Commute.all _ _)) →
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q'.app V').hom φ' (fun _ _ => Commute.all _ _))

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
