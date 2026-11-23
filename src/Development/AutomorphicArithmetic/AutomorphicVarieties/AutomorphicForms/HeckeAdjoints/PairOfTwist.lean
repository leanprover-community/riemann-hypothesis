module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

private theorem UpperTheory.V.Af.Gk.opMul_mul_invT {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}
    (χ : HChar E) (o : Op E a) : ((opMul χ o : ℂˣ) : ℂ) * ((opMul χ (invTOp o) : ℂˣ) : ℂ) = 1 := by
  have key : ∀ g : GlobalTheory.CuspRep.GA E a, ((GlobalTheory.CuspRep.chiDet a χ g : ℂˣ) : ℂ) *
      ((GlobalTheory.CuspRep.chiDet a χ (GlobalTheory.CuspRep.invT a _ g) : ℂˣ) : ℂ) = 1 := fun g => by
    rw [InvT.chiDet_invT]
    exact Units.mul_inv _
  cases o with
  | fin k =>
    have := key (GlobalTheory.CuspRep.finGL E a k)
    rw [← InvT.finGL_invT] at this
    exact this
  | cpt k =>
    have := key (infGL E a (Unitary.toUnits k))
    rw [← infGL_invT, invT_toUnits] at this
    exact this
  | lie X => simp [opMul, invTOp]

theorem UpperTheory.V.Af.Gk.pairOfTwist :
    UpperTheory.V.Af.Gk.PairOfTwist := by
  intro F _ _ _ a π χ ⟨B, h1, h2, hf, hc, hl⟩
  let T := π.toTwist χ
  refine ⟨B.compl₁₂ T.toLinearMap T.toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ h
    apply T.injective
    rw [T.map_zero]
    apply h1
    intro ψ
    simpa using h (T.symm ψ)
  · intro ψ h
    apply T.injective
    rw [T.map_zero]
    apply h2
    intro φ
    simpa using h (T.symm φ)
  · intro k φ ψ
    have h := hf k (T φ) (T ψ)
    have e := opMul_mul_invT χ (.fin k : Op F a)
    simp only [T, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [← mul_assoc, mul_comm (_ : ℂ) ((opMul χ (.fin k) : ℂˣ) : ℂ)] at h
    erw [e] at h
    rw [one_mul] at h
    exact h
  · intro k φ ψ
    have h := hc k (T φ) (T ψ)
    have e := opMul_mul_invT χ (.cpt k : Op F a)
    simp only [T, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    rw [← mul_assoc] at h
    erw [e] at h
    rw [one_mul] at h
    exact h
  · intro X φ ψ
    have h := hl X (T φ) (T ψ)
    have e : (Matrix.of (toL (-(Matrix.of X)ᵀ))).trace = -(Matrix.of X).trace := by
      change (-(Matrix.of X)ᵀ).trace = _
      rw [Matrix.trace_neg, Matrix.trace_transpose]
    simp only [T, CuspSub.op_toTwist, opAdd, opMul, Units.val_one, one_smul, map_add (f := _), map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, e, map_neg] at h
    change B (T _) (T ψ) + B (T φ) (T _) = 0
    linear_combination h
