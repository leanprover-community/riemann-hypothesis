module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isDia_conj_mem_lev : ∀ (N l : ℕ) (d : ℤ) (σ γ : SL(2, ℤ)), IsDia N l d σ → γ ∈ lev N l →
    σ * γ * σ⁻¹ ∈ lev N l := by
  intro N l d σ γ hσ hγ
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hσ.1
  have hσN : σ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      (dvd_trans (Int.natCast_dvd_natCast.2 (dvd_mul_right N l)) hc)
  have hσl : σ ∈ Gamma0 l := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2
      (dvd_trans (Int.natCast_dvd_natCast.2 (dvd_mul_left l N)) hc)
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.1 hγ
  refine Subgroup.mem_inf.2
    ⟨?_, (Gamma0 l).mul_mem ((Gamma0 l).mul_mem hσl hγ0) ((Gamma0 l).inv_mem hσl)⟩
  have hγN : γ ∈ Gamma0 N := ((Gamma1_mem N γ).1 hγ1).2.2
  set S : Gamma0 N := ⟨σ, hσN⟩
  set G : Gamma0 N := ⟨γ, hγN⟩
  have hG : G ∈ Gamma1' N := (Gamma1_to_Gamma0_mem G).2 ((Gamma1_mem N γ).1 hγ1)
  have hX : S * G * S⁻¹ ∈ Gamma1' N := by
    rw [Gamma1_mem'] at hG ⊢
    rw [map_mul, map_mul, hG, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have h := (Gamma1_to_Gamma0_mem _).1 hX
  exact (Gamma1_mem N _).2 h

end GlobalTheory.Hk
