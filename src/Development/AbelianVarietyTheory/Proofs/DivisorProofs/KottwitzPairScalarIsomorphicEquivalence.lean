module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul' (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_one' : sh G (1 : G.C) = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

theorem rel_equivalence : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Equivalence (Pair.Rel (G := G)) := by
  intro p _ G
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_, ?_⟩
    · simp [sh_one']
    · simp
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩
    · have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        rw [← sh_mul', Units.inv_mul, sh_one']
      rw [hβ]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
        inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
    · rw [hγ]; group
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    obtain ⟨y', s', hs', hβ', hγ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩
    · rw [hβ', hβ, Units.val_mul, sh_mul']
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]
    · rw [hγ', hγ]; group

end GlobalTheory.LKMid.Pair
