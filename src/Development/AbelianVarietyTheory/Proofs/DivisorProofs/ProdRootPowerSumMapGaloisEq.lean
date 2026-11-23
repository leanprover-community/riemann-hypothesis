module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMapFrobeniusPowStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem prod_rootSum_map_algEquiv : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) (k : ℕ) (P : F'[X]),
    ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) =
      ∏ j ∈ Finset.range (Module.finrank F F'), rootSum θ (k * Nat.card F ^ j) P := by
  intro F F' _ _ _ _ θ k P
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  have hb := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F'
  rw [← Fintype.prod_bijective _ hb
    (fun n => rootSum θ k (P.map ((FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1 : F' ≃ₐ[F] F') : F' →+* F')))
    _ (fun _ => rfl)]
  rw [Finset.prod_range (fun j => rootSum θ (k * Nat.card F ^ j) P)]
  refine Finset.prod_congr rfl fun n _ => ?_
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have key := GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F' θ
    ((FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1 : F' ≃ₐ[F] F') : F' →+* F') (r * n.1) (fun x => by
      rw [hchar, pow_mul, ← hcard]
      show (FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1) x = _
      rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]) k P
  rw [key, hchar, pow_mul, ← hcard, Nat.card_eq_fintype_card]

end GlobalTheory.Shin
