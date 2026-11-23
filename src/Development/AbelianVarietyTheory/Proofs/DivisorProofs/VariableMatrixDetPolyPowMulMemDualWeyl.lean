module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead

theorem detPol_mem_dualWeyl_one (R : Type) [CommRing R] (n : ℕ) :
    detPol R n ∈ dualWeyl R n n (fun _ => 1) := by
  have h := Formalism.GradedWeylDivisibility.bidetMem R n n 1 (fun _ => n) (fun _ => le_refl n) (fun _ => id)
  have hb : bideterminant R (r := n) (n := n) (fun _ : Fin 1 => n) (fun _ => le_refl n) (fun _ => id) = detPol R n := by
    simp [bideterminant, initMinor, detPol]
  have hs : shapeDeg (n := n) (fun _ : Fin 1 => n) = fun _ => 1 := by
    funext t
    simp [shapeDeg, t.isLt]
  rw [hb, hs] at h
  exact h

theorem detPol_pow_mul_mem_dualWeyl : ∀ (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R), f ∈ dualWeyl R n n ν → detPol R n ^ k * f ∈ dualWeyl R n n fun a => ν a + k := by
  intro R _ n k ν f hf
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have h := (Formalism.GradedWeylDivisibility.dualWeylMul R n n (fun _ => 1) (fun a => ν a + k) (detPol R n) (detPol R n ^ k * f)).1
      (detPol_mem_dualWeyl_one R n) ih
    have he : ((fun _ => 1) + fun a => ν a + k) = fun a : Fin n => ν a + (k + 1) := by
      funext a; simp only [Pi.add_apply]; omega
    rw [he, ← mul_assoc, ← pow_succ'] at h
    exact h

end GlobalTheory.FrameRead
