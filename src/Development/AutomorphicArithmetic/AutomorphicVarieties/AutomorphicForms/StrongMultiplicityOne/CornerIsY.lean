module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem corner_isY {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (m : ℕ) (s : R →ₙ+* S) (y : GL (Fin n) R)
    (h : IsY m y.val) :
    IsY m (GlobalTheory.CuspRep.cornerGL n s y).val ∧ supN (GlobalTheory.CuspRep.cornerGL n s y).val = s (supN y.val) := by
  have e : ∀ i j, (GlobalTheory.CuspRep.cornerGL n s y).val i j =
      (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s (y.val i j) := fun _ _ => rfl
  refine ⟨fun i hi => ⟨?_, fun j hj => ?_⟩, ?_⟩
  · rw [e, (h i hi).1]; simp
  · rw [e, (h i hi).2 j hj, Matrix.one_apply_ne hj.ne', Matrix.one_apply_ne hj.ne']; simp
  · unfold supN

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · have hne : i ≠ j := fun h' => by subst h'; omega
      rw [e, Matrix.one_apply_ne hne, Matrix.one_apply_ne hne]; simp
    · simp

theorem UpperTheory.V.Af.StrongMultiplicityOne.embY :
    UpperTheory.V.Af.StrongMultiplicityOne.EmbY := by
  intro E _ _ _ n m
  exact ⟨fun w y h => corner_isY m (sLoc E w) y h, fun y h => corner_isY m (sFin E) y h,
    fun y h => corner_isY m (sInf E) y h, fun w => GlobalTheory.CuspRep.CuspSub.continuous_locGL w⟩
