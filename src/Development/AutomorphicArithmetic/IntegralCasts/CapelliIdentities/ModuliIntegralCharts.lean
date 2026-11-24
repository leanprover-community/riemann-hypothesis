module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

private theorem UpperTheory.Reformulated.B.ModuliIntegralCharts.exists_zsmul_mem {E V : Type} [Field E] [NumberField E]
    [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (L : Submodule (𝓞 E) V) {v : V} (hv : v ∈ Submodule.span E (L : Set V)) :
    ∃ N : ℤ, N ≠ 0 ∧ (N : E) • v ∈ L := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM, hx⟩ := hx
    obtain ⟨N, hN, hy⟩ := hy
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have h : ((M * N : ℤ) : E) • (x + y) = N • ((M : E) • x) + M • ((N : E) • y) := by
      rw [← Int.cast_smul_eq_zsmul E N, ← Int.cast_smul_eq_zsmul E M ((N : E) • y), smul_smul,
        smul_smul, smul_add, Int.cast_mul, mul_comm (N : E)]
    rw [h]
    exact L.add_mem (zsmul_mem hx N) (zsmul_mem hy M)
  | smul c x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨M, hM, hint⟩ := hc.exists_integral_multiple
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    let a : 𝓞 E := ⟨M • c, hint⟩
    have ha : algebraMap (𝓞 E) E a = (M : E) * c := by
      rw [← zsmul_eq_mul]; rfl
    have h : ((M * N : ℤ) : E) • c • x = a • ((N : E) • x) := by
      rw [← algebraMap_smul E a, ha, smul_smul, smul_smul, Int.cast_mul, mul_right_comm]
    rw [h]
    exact L.smul_mem a hx

theorem UpperTheory.Reformulated.B.ModuliIntegralCharts.single_mem :
    ∀ (I : Formalism.MainNotions.S.AutInst) (i : Fin I.n), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ Pi.single i (↑N : I.E) ∈ I.L := by
  intro I i
  obtain ⟨N, hN, h⟩ := UpperTheory.Reformulated.B.ModuliIntegralCharts.exists_zsmul_mem I.L
    (v := (Pi.single i (1 : I.E) : Fin I.n → I.E)) (by rw [I.L_span]; exact Submodule.mem_top)
  refine ⟨N, hN, ?_⟩
  rwa [← Pi.single_smul', smul_eq_mul, mul_one] at h
