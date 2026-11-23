module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KSpan

def kSub {n : ℕ} (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | inK ε Y}
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨?_, ?_⟩
    · unfold inG at *
      rw [conjTranspose_add, add_mul, mul_add]
      calc _ = (aᴴ * Jm ε + Jm ε * a) + (bᴴ * Jm ε + Jm ε * b) := by abel
        _ = 0 := by rw [ha1, hb1, add_zero]
    · rw [add_mul, mul_add, ha2, hb2]
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · simp [inG]
    · simp
  smul_mem' := by
    intro t Z hZ
    have h := inK_smul_real ε hZ t
    rwa [Complex.coe_smul] at h

theorem finite_real_span : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ (r : ℕ) (X : Fin r → Mx n), (∀ j, inK ε (X j)) ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j := by
  intro n ε
  let b := Module.finBasis ℝ (kSub ε)
  refine ⟨Module.finrank ℝ (kSub ε), fun j => ((b j : kSub ε) : Matrix (Fin n) (Fin n) ℂ), fun j => (b j).2, ?_⟩
  intro Y hY
  refine ⟨fun j => b.repr ⟨Y, hY⟩ j, ?_⟩
  have h2 := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  conv_lhs => rw [← h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.coe_smul]

end GlobalTheory.KSpan
