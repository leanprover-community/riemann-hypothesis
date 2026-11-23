module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowerExamples

variable {S : Scheme.{0}}

theorem hom_ext {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) {T : Over S}
    {x y : T ⟶ G'} (h : ∀ i, x ≫ p.pr i = y ≫ p.pr i) : x = y :=
  p.lim.hom_ext fun ⟨i⟩ => h i

theorem comm_of_pow {G' G : Over S} [GrpObj G'] [GrpObj G] [IsCommMonObj G] {j : ℕ}
    (p : IsPowGrp G' G j) : IsCommMonObj G' where
  mul_comm := hom_ext p fun i => by
    have := p.hom i
    rw [Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]

theorem pow_unique {G₁ G₂ G : Over S} [GrpObj G₁] [GrpObj G₂] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G₁ G j) (q : IsPowGrp G₂ G j) :
    ∃ e : G₁ ≅ G₂, IsMonHom e.hom ∧ ∀ i, e.hom ≫ q.pr i = p.pr i := by
  have he : ∀ i, (p.lim.conePointUniqueUpToIso q.lim).hom ≫ q.pr i = p.pr i := fun i =>
    p.lim.conePointUniqueUpToIso_hom_comp q.lim ⟨i⟩
  refine ⟨p.lim.conePointUniqueUpToIso q.lim, ⟨hom_ext q fun i => ?_, hom_ext q fun i => ?_⟩, he⟩
  · have := p.hom i; have := q.hom i
    erw [Category.assoc, he i, IsMonHom.one_hom, IsMonHom.one_hom]
  · have := p.hom i; have := q.hom i
    erw [Category.assoc, he i, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom (q.pr i),
      ← Category.assoc, tensorHom_comp_tensorHom, he i]

end GlobalTheory.PowerExamples
