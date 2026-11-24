module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Filtration

@[expose] public section

namespace GlobalTheory

theorem isAdicComplete_of_le_of_isNoetherianRing (R : Type) [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (hIJ : I ≤ J) (hJ : IsAdicComplete J R) : IsAdicComplete I R := by
  have hle : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) ≤ J ^ n • ⊤ := fun n =>
    Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)
  have hH : IsHausdorff I R :=
    ⟨fun x hx => hJ.toIsHausdorff.haus x fun n => (hx n).mono (hle n)⟩
  have hP : IsPrecomplete I R := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := hJ.toIsPrecomplete.prec (f := f) fun {m n} h => (hf h).mono (hle m)
    refine ⟨L, fun n => ?_⟩
    set N : Submodule R R := I ^ n • ⊤ with hN
    have hK : (⨅ m : ℕ, J ^ m • ⊤ : Submodule R (R ⧸ N)) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_le_jacobson J (by
        simpa only [Ideal.jacobson_bot] using IsAdicComplete.le_jacobson_bot J)
    rw [SModEq.sub_mem, ← Submodule.Quotient.mk_eq_zero, ← Submodule.mem_bot R, ← hK,
      Submodule.mem_iInf]
    intro m
    have h1 : f n - f (max n m) ∈ N := SModEq.sub_mem.1 (hf (le_max_left n m))
    have h2 : f (max n m) - L ∈ (J ^ m • ⊤ : Submodule R R) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right n m))
        (SModEq.sub_mem.1 (hL (max n m)))
    have h3 : N.mkQ (f (max n m) - L) ∈ (J ^ m • ⊤ : Submodule R (R ⧸ N)) := by
      have := Submodule.mem_map_of_mem (f := N.mkQ) h2
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have h4 : (Submodule.Quotient.mk (f n - L) : R ⧸ N) = N.mkQ (f (max n m) - L) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
      convert h1 using 1
      ring
    rw [h4]
    exact h3
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

end GlobalTheory
