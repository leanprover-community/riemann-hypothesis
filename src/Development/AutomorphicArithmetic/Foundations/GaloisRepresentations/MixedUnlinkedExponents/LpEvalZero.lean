module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf
import Formalism.DoubleCosetMeasures.Statement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

private theorem lp_zero' : UpperTheory.Gal.GamX.lp (0 : Multiset ℂˣ) = 1 := by
  simp [UpperTheory.Gal.GamX.lp]

private theorem lp_cons' (a : ℂˣ) (A : Multiset ℂˣ) :
    UpperTheory.Gal.GamX.lp (a ::ₘ A) = (1 - Polynomial.C (a : ℂ) * Polynomial.X) * UpperTheory.Gal.GamX.lp A := by
  simp [UpperTheory.Gal.GamX.lp]

private theorem lp_eval_zero (A : Multiset ℂˣ) : (UpperTheory.Gal.GamX.lp A).eval 0 = 1 := by
  induction A using Multiset.induction_on with
  | empty => simp [lp_zero']
  | cons a A ih => rw [lp_cons', Polynomial.eval_mul, ih]; simp

private theorem lp_ne_zero (A : Multiset ℂˣ) : UpperTheory.Gal.GamX.lp A ≠ 0 := by
  intro h
  have h1 := lp_eval_zero A
  rw [h] at h1
  simp at h1

private theorem lin_eq (a : ℂˣ) :
    (1 - Polynomial.C (a : ℂ) * Polynomial.X : ℂ[X]) =
      Polynomial.C (-(a : ℂ)) * (Polynomial.X - Polynomial.C ((a⁻¹ : ℂˣ) : ℂ)) := by
  have ha : (a : ℂ) ≠ 0 := a.ne_zero
  rw [Units.val_inv_eq_inv_val, mul_sub, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ ha,
    Polynomial.C_neg, Polynomial.C_neg, Polynomial.C_1]
  ring

private theorem lin_roots (a : ℂˣ) :
    (1 - Polynomial.C (a : ℂ) * Polynomial.X : ℂ[X]).roots = {((a⁻¹ : ℂˣ) : ℂ)} := by
  rw [lin_eq, Polynomial.roots_C_mul _ (by simp), Polynomial.roots_X_sub_C]

private theorem lp_roots (A : Multiset ℂˣ) :
    (UpperTheory.Gal.GamX.lp A).roots = A.map (fun a => ((a⁻¹ : ℂˣ) : ℂ)) := by
  induction A using Multiset.induction_on with
  | empty => simp [lp_zero']
  | cons a A ih =>
    rw [lp_cons', Polynomial.roots_mul (by rw [← lp_cons']; exact lp_ne_zero _), lin_roots, ih,
      Multiset.map_cons, Multiset.singleton_add]

theorem UpperTheory.Gal.GamX.lpInj :
    UpperTheory.Gal.GamX.LpInj := by
  intro A B h
  have h1 := congrArg Polynomial.roots h
  rw [lp_roots, lp_roots] at h1
  exact Multiset.map_injective (fun a b hab => inv_injective (Units.ext hab)) h1
