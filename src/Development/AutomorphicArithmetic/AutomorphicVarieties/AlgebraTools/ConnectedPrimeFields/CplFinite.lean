module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
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
public import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.cplFinite :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [CommRing B]
      [IsLocalRing B] [Algebra A B] [Module.Finite A B] (I : Ideal B), I ≠ ⊤ → IsAdicComplete I B := by
  intro A B _ _ _ _ _ _ _ _ I hI
  have hN : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have hc : IsAdicComplete (maximalIdeal B) B := by
    exact GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local A B
  have hle : I ≤ maximalIdeal B := le_maximalIdeal hI
  have hH : IsHausdorff I B := IsHausdorff.of_isLocalRing _ _ hI
  have hP : IsPrecomplete I B := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec (f := f) (fun {m n} h =>
      (hf h).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hle m)))
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, ← Submodule.Quotient.mk_eq_zero]
    have hq : IsHausdorff (maximalIdeal B) (B ⧸ (I ^ n • (⊤ : Submodule B B))) :=
      IsHausdorff.of_isLocalRing _ _ (maximalIdeal.isMaximal B).ne_top
    refine hq.haus _ fun k => ?_
    rw [SModEq.zero]
    have h1 : f n - f (n + k) ∈ I ^ n • (⊤ : Submodule B B) := SModEq.sub_mem.1 (hf (Nat.le_add_right n k))
    have h2 : f (n + k) - L ∈ maximalIdeal B ^ k • (⊤ : Submodule B B) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_left k n)) (SModEq.sub_mem.1 (hL (n + k)))
    have e : f n - L = (f n - f (n + k)) + (f (n + k) - L) := by ring
    rw [e, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 h1, zero_add]
    have h3 := Submodule.mem_map_of_mem (f := (I ^ n • (⊤ : Submodule B B)).mkQ) h2
    rw [Submodule.map_smul''] at h3
    exact Submodule.smul_mono le_rfl le_top h3
  exact { }
