module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfWeierstrassPDerivWeierstrassPTorsionEqStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.SepGL

theorem vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (hx : x ≠ 0) (α : GL (Fin 2) (ZMod N)) :
    vmul x α ≠ 0 := by
  intro h
  apply hx
  have h2 : (x ᵥ* (α : Matrix (Fin 2) (Fin 2) (ZMod N))) ᵥ*
      ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  unfold vmul at h
  rw [← h2, h, Matrix.zero_vecMul]

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (α β : GL (Fin 2) (ZMod N)), (∀ i : Fin 2, wp N (vmul (Pi.single i 1) α) τ = wp N (vmul (Pi.single i 1) β) τ ∧ wpd N (vmul (Pi.single i 1) α) τ = wpd N (vmul (Pi.single i 1) β) τ) → α = β := by
  intro N _ τ α β h
  rcases subsingleton_or_nontrivial (ZMod N) with hs | hs
  · exact Matrix.GeneralLinearGroup.ext fun i j => Subsingleton.elim _ _
  · have key : ∀ i : Fin 2, vmul (Pi.single i 1) α = vmul (Pi.single i 1) β := by
      intro i
      have h0 : (Pi.single i (1 : ZMod N) : Fin 2 → ZMod N) ≠ 0 := by
        intro h1
        have := congrFun h1 i
        simp at this
      exact GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq N τ _ _ (vmul_ne_zero _ h0 α) (vmul_ne_zero _ h0 β) (h i).1 (h i).2
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    have := congrFun (key i) j
    simpa [vmul, Matrix.single_vecMul] using this

end GlobalTheory.WpFam.SepGL
