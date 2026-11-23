module

public import Development.EtaleCohomology.EtaleTrace.TorsionH0PointOfLocalTwist
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem freeGen_nat (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (ULift.up x : uliftFunctor.{1, 0}.obj (P.obj (op U)))))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h
  simp only [Sec.res, freeGen]
  refine h.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)))
    (by simp only [freeP, ModuleCat.freeMk, ModuleCat.free, Functor.comp_obj, Functor.whiskeringRight_obj_obj, Functor.comp_map]
        exact Finsupp.mapDomain_single)

theorem evNat : EvNat := by
  intro R _ F X U α x
  have h := freeGen_nat R ((sch.obj X).obj (op (SimplexCategory.mk 0))) x (𝟙 X : Sx (sch.obj X) 0 X)
  have hx : ((sch.obj X).obj (op (SimplexCategory.mk 0))).map x.op (𝟙 X : Sx (sch.obj X) 0 X) = (x : Sx (sch.obj X) 0 U) :=
    Category.comp_id x
  rw [hx] at h
  simp only [ev]
  rw [← h]
  simp only [Sec.res]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

end LateralTheory.EtaleTrace
