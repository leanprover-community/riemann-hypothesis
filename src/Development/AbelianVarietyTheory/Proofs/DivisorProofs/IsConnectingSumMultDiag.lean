module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoConvMulSymmetricCocycle
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

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

namespace GlobalTheory

namespace PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
  [IsCocomm R A] [IsCocomm R B]


variable (R A) in
abbrev multDiag (i : ℕ) : A ⊗[R] A →ₐ[R] A :=
  Algebra.TensorProduct.lift (mulBy R A i : A →ₐ[R] A) (AlgHom.id R _) (fun _ _ ↦ Commute.all _ _)


variable (R A) in
abbrev valZero : A ⊗[R] A →ₐ[R] R :=
  Algebra.TensorProduct.lift (counitAlgHom R A) (counitAlgHom R A) (fun _ _ ↦ Commute.all _ _)


theorem pullTwo_mulBy_eq (c : A ⊗[R] A) (hc : c ∈ symCocycles R A) (k : ℕ) :
    pullbackTwo (mulBy R A k) c = algebraMap R _ (valZero R A c) + k • c +
      cobOne R A (∑ i ∈ Finset.range k, multDiag R A i c) := by
  induction k with
  | zero =>
    have h0 : ∀ a : A, mulBy R A 0 a = algebraMap R A (counit a) := fun _ => rfl
    rw [Finset.sum_range_zero, map_zero, zero_smul, add_zero, add_zero]
    generalize c = t
    induction t with
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
    | tmul a b =>
      simp [h0, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
        smul_smul, mul_comm]
  | succ k ih =>
    have h := pullTwo_convMul (mulBy R A k) (BialgHom.id R A) c hc
    have e : (toConv (mulBy R A k) * toConv (BialgHom.id R A)).ofConv = mulBy R A (k + 1) := by
      rw [mulBy, mulBy, pow_succ]
    have e2 : ∀ t : A ⊗[R] A, LinearMap.mul' R A (TensorProduct.map (mulBy R A k : A →ₗ[R] A)
        (BialgHom.id R A : A →ₗ[R] A) t) = multDiag R A k t := fun t => by
      induction t with
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
      | tmul a b => simp
    rw [e, e2, pullTwo_id, ih] at h
    rw [h, Finset.sum_range_succ, map_add (f := _), succ_nsmul]
    abel

end PDiv

namespace PDivGroup

open PDiv

end PDivGroup

end GlobalTheory
