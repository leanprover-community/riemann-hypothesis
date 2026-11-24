module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteMulByNatAbelianVarietyAlgClosedStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbTorsionFinite

theorem finite_fibre_points {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType X.hom] (f : X ⟶ Y)
    [IsFinite f.left] (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y) :
    Finite {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X // x ≫ f = y} := by
  have hfin : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}).Finite :=
    f.left.finite_preimage_singleton _
  have := hfin.to_subtype
  refine Finite.of_injective
    (fun x => (⟨x.1.left (IsLocalRing.closedPoint K), by
      have h := congrArg (fun u => u.left (IsLocalRing.closedPoint K)) x.2
      exact h⟩ : (f.left ⁻¹' {y.left (IsLocalRing.closedPoint K)}))) ?_
  intro a b hab
  refine Subtype.ext (Over.OverMorphism.ext ?_)
  exact ext_of_apply_closedPoint_eq (K := K) X.hom (Over.w a.1) (Over.w b.1)
    (congrArg Subtype.val hab)

theorem finite_torsion : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B // x ^ n = 1} := by
  intro K _ _ B _ hB n hn
  have := GlobalTheory.T.isFinite_mulByNat_abelianVariety_algClosed K B hB n hn
  have : IsProper B.hom := hB.proper
  have := finite_fibre_points (mulA B n) 1
  refine Finite.of_equiv _ (Equiv.subtypeEquivRight (p := fun x => x ≫ mulA B n = 1) fun x => ?_)
  have : x ≫ mulA B n = x ^ n := by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  rw [this]

end GlobalTheory.AbTorsionFinite
