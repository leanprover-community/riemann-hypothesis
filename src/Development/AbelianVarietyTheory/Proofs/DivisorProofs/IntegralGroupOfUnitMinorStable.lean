module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
import Formalism.DoubleCosetMeasures.Statement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

noncomputable section

namespace GlobalTheory.FullRankCoinv.UnitMinor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adjugate_integral {n : ℕ} (X : Matrix (Fin n) (Fin n) k) (hX : ∀ i j, X i j ∈ 𝒪[k]) :
    ∀ i j, X.adjugate i j ∈ 𝒪[k] := by
  let X' : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨X i j, hX i j⟩
  have e : X = (algebraMap 𝒪[k] k).mapMatrix X' := by ext i j; rfl
  intro i j
  rw [e, ← RingHom.map_adjugate]
  exact (X'.adjugate i j).2

theorem mul_integral {a b c : ℕ} (X : Matrix (Fin a) (Fin b) k) (W : Matrix (Fin b) (Fin c) k)
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hW : ∀ i j, W i j ∈ 𝒪[k]) : ∀ i j, (X * W) i j ∈ 𝒪[k] := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hX i l) (hW l j)

theorem integral_of_mul {n d : ℕ} (M : Matrix (Fin n) (Fin n) k) (Z : Matrix (Fin n) (Fin d) k)
    (hZ : Z ∈ unitMinorSet k n d) (hMZ : ∀ i j, (M * Z) i j ∈ 𝒪[k]) : ∀ i j, M i j ∈ 𝒪[k] := by
  obtain ⟨hZi, f, hf⟩ := hZ
  set Zf := Z.submatrix id f with hZf
  have hsub : (M * Z).submatrix id f = M * Zf := by
    ext i j; simp [Zf, Matrix.mul_apply]
  have hdet : Zf.det ≠ 0 := by
    intro h0; rw [h0, map_zero] at hf; exact zero_ne_one hf
  have hM : M = (M * Z).submatrix id f * Zf⁻¹ := by
    rw [hsub, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.mul_one]
  have hZfi : ∀ i j, Zf i j ∈ 𝒪[k] := fun i j => hZi _ _
  have hinv : ∀ i j, Zf⁻¹ i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
    refine Subring.mul_mem _ ?_ (adjugate_integral Zf hZfi i j)
    rw [Valuation.mem_integer_iff, map_inv₀, hf, inv_one]
  rw [hM]
  exact mul_integral _ _ (fun i j => hMZ _ _) hinv

theorem mem_KO_of_mul_mem_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k) (hY : Y ∈ unitMinorSet k n d)
    (hEY : E.val * Y ∈ unitMinorSet k n d) : E ∈ GlobalTheory.SplitWeil.KO k (Fin n) := by
  refine (mem_KO_iff E).2 ⟨integral_of_mul _ Y hY hEY.1, integral_of_mul _ (E.val * Y) hEY ?_⟩
  rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  exact hY.1

end GlobalTheory.FullRankCoinv.UnitMinor
