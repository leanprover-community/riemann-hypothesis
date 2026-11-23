module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.repM_apply_zt_eq_pow_redTop :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N] (y : (ZMod (topM l n m (N * N)))ˣ), (repM (topM l n m (N * N)) y : Ω ≃ₐ[ℚ] Ω) (zt ε l (m + n)) = zt ε l (m + n) ^ ((redTop l n m N y : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n))).val := by
  intro Ω _ _ _ ε l hl n m N _ y
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl0 : l ^ (m + n) ≠ 0 := pow_ne_zero _ hl.out.ne_zero
  haveI : NeZero (l ^ (m + n)) := ⟨hl0⟩
  have h1 : zt ε l (m + n) ^ (l ^ (m + n)) = 1 := by
    have h := (isPrimitiveRoot_eOm ε hl0).pow_eq_one
    rw [Nat.cast_pow] at h
    exact h
  have hd : l ^ (m + n) ∣ topM l n m (N * N) := Dvd.intro _ rfl
  have h2 : zt ε l (m + n) ^ topM l n m (N * N) = 1 := by
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, h1, one_pow]
  rw [repM_apply _ y h2]
  have e : ((redTop l n m N y : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n))) =
      (((y : ZMod (topM l n m (N * N))).val : ℕ) : ZMod (l ^ (m + n))) := by
    show ZMod.castHom hd (ZMod (l ^ (m + n))) (y : ZMod (topM l n m (N * N))) = _
    rw [ZMod.castHom_apply, ZMod.natCast_val]
  rw [e, ZMod.val_natCast, ← pow_eq_pow_mod _ h1]
