module

public import Formalism.CharacterColumnKernels.Statement
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset Polynomial

noncomputable section

namespace Formalism.NG

def matEnd (O M : Type*) [CommRing O] [AddCommGroup M] [Module O M] (d : Type*) [Fintype d]
    [DecidableEq d] : Matrix d d O →+* Module.End O (d → M) where
  toFun A := relMap O M A
  map_one' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap, Matrix.one_apply, ite_smul, Finset.sum_ite_eq]
  map_mul' A B := by
    refine LinearMap.ext fun v => funext fun i => ?_
    show (∑ j, (A * B) i j • v j) = ∑ k, A i k • ∑ j, B k j • v j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  map_zero' := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap]
  map_add' A B := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [relMap, add_smul, Finset.sum_add_distrib]

def LatQ {R : Type*} [Ring R] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (d : Type*) [Fintype d] [DecidableEq d] (_ρ : R →+* Matrix d d O) : Type _ := d → KO O

section LatQ
variable {R : Type*} [Ring R] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (d : Type*) [Fintype d] [DecidableEq d] (ρ : R →+* Matrix d d O)

instance : AddCommGroup (LatQ O d ρ) := inferInstanceAs (AddCommGroup (d → KO O))
instance : Module O (LatQ O d ρ) := inferInstanceAs (Module O (d → KO O))
instance : Module R (LatQ O d ρ) :=
  Module.compHom (d → KO O) ((matEnd O (KO O) d).comp ρ)

end LatQ

def StatKerHomRect : Prop :=
  ∀ (R O : Type*) [Ring R] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m g d : Type) [Fintype m] [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
    (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)] (P : Matrix m g R),
    Module.length O (LinearMap.ker (relMap O (KO O)
        (fun (p : m × d) (q : g × d) => ρ (P p.1 q.1) p.2 q.2))) =
      Module.length O (Coker P →ₗ[R] LatQ O d ρ)

end Formalism.NG
