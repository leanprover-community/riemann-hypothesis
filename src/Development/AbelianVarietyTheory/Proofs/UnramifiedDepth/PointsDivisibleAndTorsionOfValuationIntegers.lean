module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
public import ReciprocityTheory.DualLattices.SqZeroOfSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.FormalChartAtZero

@[expose] public section

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem torsVal_valuationRing {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C]
    {v : Valuation C NNReal} (hv : v.Integers O) : ValuationRing O := by
  refine @ValuationRing.mk _ _ _ ⟨fun a b => ?_⟩
  rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inr hc.symm⟩
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hv h
    exact ⟨c, Or.inl hc.symm⟩

private theorem torsVal_exists_point {Ω : Type} [Field Ω] [IsAlgClosed Ω] {P A : Scheme.{0}}
    (ψ : P ⟶ A) [LocallyOfFiniteType ψ] [Surjective ψ] (x : Spec (CommRingCat.of Ω) ⟶ A) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ P, p ≫ ψ = x := by
  have hJ : JacobsonSpace ↥(Limits.pullback ψ x) :=
    LocallyOfFiniteType.jacobsonSpace (Limits.pullback.snd ψ x)
  obtain ⟨w⟩ : Nonempty ↥(Spec (CommRingCat.of Ω)) := inferInstance
  obtain ⟨z₀, -⟩ := (Limits.pullback.snd ψ x).surjective w
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(Limits.pullback ψ x)))
    ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed
  replace hz : IsClosed {z} := hz
  refine ⟨pointOfClosedPoint (Limits.pullback.snd ψ x) z hz ≫ Limits.pullback.fst _ _, ?_⟩
  rw [Category.assoc, Limits.pullback.condition, pointOfClosedPoint_comp_assoc]

private theorem torsVal_lift {R₀ : Type} [CommRing R₀] {X Y : Over (Spec (CommRingCat.of R₀))}
    (m : X ⟶ Y) [IsFinite m.left] {O C : Type} [CommRing O] [Field C] [Algebra R₀ O] [Algebra O C]
    [Algebra R₀ C] [IsScalarTower R₀ O C] {v : Valuation C NNReal} (hv : v.Integers O)
    (x : sp (R₀ := R₀) O ⟶ Y) (z : sp (R₀ := R₀) C ⟶ X)
    (h : z ≫ m = spMap (IsScalarTower.toAlgHom R₀ O C) ≫ x) :
    ∃! y : sp (R₀ := R₀) O ⟶ X, y ≫ m = x ∧ spMap (IsScalarTower.toAlgHom R₀ O C) ≫ y = z := by
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := torsVal_valuationRing hv
  haveI : IsFractionRing O C := hv.isFractionRing
  have hE : ValuativeCriterion.Existence m.left := by
    have h : UniversallyClosed m.left := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hU : ValuativeCriterion.Uniqueness m.left := IsSeparated.valuativeCriterion m.left
  let S : ValuativeCommSq m.left :=
    { R := O, K := C, i₁ := z.left, i₂ := x.left, commSq := ⟨congrArg Over.Hom.left h⟩ }
  obtain ⟨⟨l, h1, h2⟩⟩ := hE S
  have hw : l ≫ X.hom = (sp (R₀ := R₀) O).hom := by
    rw [← Over.w m, ← Category.assoc, h2]
    exact Over.w x
  refine ⟨Over.homMk l hw, ⟨Over.OverMorphism.ext h2, Over.OverMorphism.ext h1⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  have := (hU S).elim ⟨y.left, congrArg Over.Hom.left hy2, congrArg Over.Hom.left hy1⟩ ⟨l, h1, h2⟩
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)

private theorem torsVal_comp_pow {R₀ : Type} [CommRing R₀] {G T : Over (Spec (CommRingCat.of R₀))}
    [GrpObj G] (y : T ⟶ G) (p : ℕ) : y ≫ ((𝟙 G) ^ p : G ⟶ G) = y ^ p := by
  rw [MonObj.comp_pow, Category.comp_id]

theorem points_divisible_and_torsion_of_valuation_integers :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (O : LAlg R₀) (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) [Algebra (O : Type) C] [Algebra R₀ C] [IsScalarTower R₀ (O : Type) C] (p : ℕ), v.Integers (O : Type) → IsFinite ((𝟙 G) ^ p : G ⟶ G).left → Surjective ((𝟙 G) ^ p : G ⟶ G).left →
    (∀ x : sp (R₀ := R₀) (O : Type) ⟶ G, ∃ y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = x) ∧
    ∀ z : sp (R₀ := R₀) C ⟶ G, z ^ p = 1 → ∃! y : sp (R₀ := R₀) (O : Type) ⟶ G, y ^ p = 1 ∧ spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ y = z) := by
  intro R₀ _ G _ _ O C _ _ _ v _ _ _ p hv hfin hsurj
  refine ⟨fun x => ?_, fun z hz => ?_⟩
  · obtain ⟨w, hw⟩ := torsVal_exists_point ((𝟙 G) ^ p : G ⟶ G).left
      (spMap (IsScalarTower.toAlgHom R₀ (O : Type) C) ≫ x).left
    have hw' : w ≫ G.hom = (sp (R₀ := R₀) C).hom := by
      rw [← Over.w ((𝟙 G) ^ p : G ⟶ G), ← Category.assoc, hw]
      exact Over.w _
    obtain ⟨y, ⟨hy, -⟩, -⟩ := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv x (Over.homMk w hw')
      (Over.OverMorphism.ext hw)
    exact ⟨y, by rw [← torsVal_comp_pow, hy]⟩
  · have := torsVal_lift ((𝟙 G) ^ p : G ⟶ G) hv 1 z
      (by rw [torsVal_comp_pow, hz, MonObj.comp_one])
    simpa only [torsVal_comp_pow] using this

end GlobalTheory
