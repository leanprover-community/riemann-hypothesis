module

public import Development.EtaleCohomology.EtaleSheaves.ClsBiprodEqZero
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

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC
namespace LateralTheory.E.BinPfChains
variable (R : Type) [CommRing R]
instance freeModPres : PreservesColimitsOfShape (Discrete WalkingPair) (ModuleCat.free.{1} (ULift.{1} R)) := by
  have := (ModuleCat.adj.{1} (ULift.{1} R)).leftAdjoint_preservesColimits
  infer_instance
instance freePres : PreservesColimitsOfShape (Discrete WalkingPair) (free R) := by unfold free freeP; infer_instance
instance whPres : PreservesColimitsOfShape (Discrete WalkingPair) ((SimplicialObject.whiskering PSh (Shv R)).obj (free R)) := by
  change PreservesColimitsOfShape (Discrete WalkingPair) ((Functor.whiskeringRight _ _ _).obj (free R))
  infer_instance
instance chainsPres : PreservesColimitsOfShape (Discrete WalkingPair) (chains R) := by
  unfold chains chainsN; infer_instance
theorem chainsCoprod : LateralTheory.E.BinPf.ChainsCoprod := by
  intro R _ U V
  have h : IsIso (coprodComparison (chains R) U V) := inferInstance
  have e : biprod.desc ((chains R).map (coprod.inl : U ⟶ U ⨿ V)) ((chains R).map (coprod.inr : V ⟶ U ⨿ V)) =
      (biprod.isoCoprod _ _).hom ≫ coprodComparison (chains R) U V := by
    apply biprod.hom_ext' <;> simp [coprodComparison, coprod.inl_desc, coprod.inr_desc]
  rw [e]; infer_instance

theorem bin_of (hD : LateralTheory.E.BinPf.DescEqv) : LateralTheory.E.ProdAcycPf.Bin :=
  LateralTheory.E.ProdAcycPf.Bin_of hD chainsCoprod

end LateralTheory.E.BinPfChains
