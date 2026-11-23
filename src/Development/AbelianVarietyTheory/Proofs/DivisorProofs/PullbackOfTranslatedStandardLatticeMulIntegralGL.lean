module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.KapOrb

theorem entry_mem_of_mem_GLint {L : Type} [Field L] {n : ℕ} {O : Subring L} {k : GL (Fin n) L}
    (hk : k ∈ GLint (Fin n) O) (i j : Fin n) : (k : Matrix (Fin n) (Fin n) L) i j ∈ O := by
  obtain ⟨k0, rfl⟩ := hk
  exact (k0.val i j).2

theorem mulVec_mem_of_mem_GLint {L : Type} [Field L] {n : ℕ} {O : Subring L} {k : GL (Fin n) L}
    (hk : k ∈ GLint (Fin n) O) {v : Fin n → L} (hv : ∀ i, v i ∈ O) (i : Fin n) :
    ((k : Matrix (Fin n) (Fin n) L) *ᵥ v) i ∈ O := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (entry_mem_of_mem_GLint hk i j) (hv j)

theorem pullLat_mul_of_mem_KGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → pullLat w B ψ (g * k) = pullLat w B ψ g := by
  intro E _ _ _ w K B n ψ g k hk
  have hk' : k⁻¹ ∈ GlobalTheory.LFun.KGL w (n := n) := inv_mem hk
  ext y
  show (∀ (c : K.O) (i : Fin n), (((g * k)⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E) ↔
    (∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E)
  simp only [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · intro h c i
    have e : (g⁻¹ : GLw n w).val *ᵥ ψ (c • y) =
        (k : Matrix (Fin n) (Fin n) (w.adicCompletion E)) *ᵥ ((k⁻¹ : GLw n w).val *ᵥ ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y))) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem_of_mem_GLint hk (fun j => h c j) i
  · intro h c i
    exact mulVec_mem_of_mem_GLint hk' (fun j => h c j) i

end GlobalTheory.KapOrb
