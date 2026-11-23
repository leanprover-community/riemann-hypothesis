module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let f : R →ₛₗ[(e : R →+* S)] S :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun a b => by simp [smul_eq_mul] }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

private theorem length_stalk_eq_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (x : X) (y : Y) (h : f x = y) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) = Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y) := by
  subst h
  have : IsIso (f.stalkMap x) := inferInstance
  exact (length_self_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).symm

theorem UpperTheory.Gal.TranscendenceTraces.multSec_of :
    MultSec := by
  intro V Ω _ _ r z hz
  haveI : IsIso (z ≫ r) := by rw [hz]; infer_instance
  haveI : IsIso (pullback.fst r (z ≫ r)) := inferInstance
  unfold mult
  rw [length_stalk_eq_of_isIso (pullback.fst r (z ≫ r)) _ (pt z)
    (by rw [← pt_comp, pullback.lift_fst])]
