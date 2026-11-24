module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotModelTrans
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.SS.exists_complete_dvr_finite_extension : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L], ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : Algebra V W) (_ : Algebra W L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ Module.Finite V W ∧ Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W) ∧ (∀ x : L, RingHom.IsIntegralElem ((algebraMap K L).comp (algebraMap V K)) x → x ∈ Set.range (algebraMap W L)) ∧ ∀ (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] Q, _root_.GlobalTheory.SS.PotModel W L ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A) Q → _root_.GlobalTheory.SS.PotModel V K A Q := by
  intro V K _ _ _ _ _ _ _ _ L _ _ _
  classical
  letI : Algebra V L := ((algebraMap K L).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq' rfl
  have hinj : Function.Injective (algebraMap V L) :=
    (algebraMap K L).injective.comp (IsFractionRing.injective V K)
  haveI : CharZero V := (algebraMap V K).charZero
  haveI : FaithfulSMul V L := (faithfulSMul_iff_algebraMap_injective V L).mpr hinj
  haveI : Algebra.IsAlgebraic V L := (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
  haveI : Module.Finite V (integralClosure V L) := IsIntegralClosure.finite V K L (integralClosure V L)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := V) (M := integralClosure V L)
  obtain ⟨W, _, hc, -, hfin, -, hloc, -, hint⟩ :=
    _root_.GlobalTheory.exists_complete_dvr_finite_subalgebra V L (t.image Subtype.val)
  have hcl : ∀ x : L, IsIntegral V x → x ∈ W := by
    intro x hx
    have key : ∀ y ∈ Submodule.span V (t : Set (integralClosure V L)), (y : L) ∈ W := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hint _ (Finset.mem_image_of_mem _ hy) y.2
      | zero => exact W.zero_mem
      | add a b _ _ ha hb => exact W.add_mem ha hb
      | smul r a _ ha => exact W.smul_mem ha r
    exact key ⟨x, hx⟩ (by rw [ht]; trivial)
  have hWint : ∀ w : W, IsIntegral V (w : L) := fun w =>
    (Algebra.IsIntegral.isIntegral (R := V) w).map W.val
  haveI : IsIntegralClosure W V L :=
    ⟨Subtype.val_injective, fun {x} => ⟨fun hx => ⟨⟨x, hcl x hx⟩, rfl⟩, by
      rintro ⟨w, rfl⟩
      exact hWint w⟩⟩
  haveI : IsFractionRing W L :=
    IsIntegralClosure.isFractionRing_of_algebraic V W (fun x hx => hinj (by rw [hx, map_zero]))
  have hcomp : (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) :=
    RingHom.ext fun _ => rfl
  refine ⟨W, inferInstance, inferInstance, ‹_›, hc, inferInstance, inferInstance, inferInstance,
    hcomp, hfin, fun a b h => hinj (congrArg Subtype.val h), hloc,
    fun x hx => ⟨⟨x, hcl x hx⟩, rfl⟩, ?_⟩
  intro A _ Q hP
  exact _root_.GlobalTheory.SS.potModel_trans V K W L hcomp hfin hloc A _
    (pullback.fst _ _) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A _) Q hP

end GlobalTheory.SS
