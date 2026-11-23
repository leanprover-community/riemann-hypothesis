module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulStrictMono
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cntconj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Nearcoord
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Scinv
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.nearvec :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (A : Matrix (Fin N) (Fin N) (𝓞 L)), A.det ≠ 0 →
    (nearVec A).Finite ∧ (nearVec A).ncard ≤ (2 * RR L N + 1) ^ dd L N := by
  intro L _ _ _ N A hA
  obtain ⟨hpos, B, hAB, _⟩ := scinv L N A hA
  obtain ⟨hSf, hSc⟩ := cntconj L (RR L N)
  let T : Finset (Fin N → 𝓞 L) := Fintype.piFinset fun _ => hSf.toFinset
  have hmaps : ∀ y ∈ nearVec A, (fun v : Fin N → 𝓞 L => B *ᵥ v) y ∈ (T : Set (Fin N → 𝓞 L)) := by
    intro y hy
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro a
    rw [Set.Finite.mem_toFinset]
    exact fun w => nearcoord L N A B hA hAB y hy w a
  have hc : ((nrmDet A : ℕ) : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hinj : Function.Injective (fun v : Fin N → 𝓞 L => B *ᵥ v) := by
    intro y y' h
    have h' := congrArg (fun v => A *ᵥ v) h
    simp only [Matrix.mulVec_mulVec, hAB, Matrix.smul_mulVec, Matrix.one_mulVec] at h'
    exact smul_right_injective _ hc h'
  refine ⟨(T.finite_toSet.preimage hinj.injOn).subset hmaps, ?_⟩
  calc (nearVec A).ncard ≤ (T : Set (Fin N → 𝓞 L)).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj.injOn T.finite_toSet
    _ = hSf.toFinset.card ^ N := by
        rw [Set.ncard_coe_finset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
    _ ≤ ((2 * RR L N + 1) ^ Module.finrank ℚ L) ^ N := by
        apply Nat.pow_le_pow_left
        rw [← Set.ncard_eq_toFinset_card _ hSf]
        exact hSc
    _ = (2 * RR L N + 1) ^ dd L N := by rw [← pow_mul]
