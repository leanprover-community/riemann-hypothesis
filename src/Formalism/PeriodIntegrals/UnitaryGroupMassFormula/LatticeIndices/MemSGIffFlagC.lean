module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.RowFlagIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSpanSingle
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {m : ℕ}

def FlagC (M : Matrix n n K) (v : Fin m → n → K) : Prop :=
  ∀ b, M *ᵥ v b - v b ∈ Submodule.span K (v '' {a | a < b})

theorem span_mulVec (M : Matrix n n K) {w : n → K} {S : Set (n → K)} (h : w ∈ Submodule.span K S) :
    M *ᵥ w ∈ Submodule.span K ((fun u => M *ᵥ u) '' S) := by
  have e : (fun u => M *ᵥ u) = ⇑(Matrix.mulVecLin M) := rfl
  rw [e, Submodule.span_image]
  exact Submodule.mem_map_of_mem h

theorem flagC_conj_imp (P Pi M : Matrix n n K) (hP : Pi * P = 1) (v : Fin m → n → K) (h : FlagC M v) :
    FlagC (P * M * Pi) (fun b => P *ᵥ v b) := by
  intro b
  have h1 : (P * M * Pi) *ᵥ (P *ᵥ v b) - P *ᵥ v b = P *ᵥ (M *ᵥ v b - v b) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hP, Matrix.mul_one, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec]
  rw [h1]
  have h2 := span_mulVec P (h b)
  rwa [Set.image_image] at h2

theorem flagC_conj (P Pi M : Matrix n n K) (hP : Pi * P = 1) (hP' : P * Pi = 1) (v : Fin m → n → K) :
    FlagC (P * M * Pi) (fun b => P *ᵥ v b) ↔ FlagC M v := by
  refine ⟨fun h => ?_, flagC_conj_imp P Pi M hP v⟩
  have h2 := flagC_conj_imp Pi P (P * M * Pi) hP' (fun b => P *ᵥ v b) h
  have e1 : Pi * (P * M * Pi) * P = M := by
    simp only [← Matrix.mul_assoc, hP, Matrix.one_mul]
    rw [Matrix.mul_assoc, hP, Matrix.mul_one]
  have e2 : (fun b => Pi *ᵥ (P *ᵥ v b)) = v := by
    funext b
    rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  rw [e1, e2] at h2
  exact h2

theorem span_smul_eq (c : Fin m → K) (hc : ∀ b, c b ≠ 0) (v : Fin m → n → K) (s : Set (Fin m)) :
    Submodule.span K ((fun b => c b • v b) '' s) = Submodule.span K (v '' s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have e : v b = (c b)⁻¹ • (c b • v b) := by rw [smul_smul, inv_mul_cancel₀ (hc b), one_smul]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)

theorem flagC_smul (M : Matrix n n K) (c : Fin m → K) (hc : ∀ b, c b ≠ 0) (v : Fin m → n → K) :
    FlagC M (fun b => c b • v b) ↔ FlagC M v := by
  unfold FlagC
  simp only [span_smul_eq c hc v, Matrix.mulVec_smul, ← smul_sub]
  refine forall_congr' (fun b => ⟨fun h => ?_, fun h => Submodule.smul_mem _ _ h⟩)
  have h3 := Submodule.smul_mem _ (c b)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ (hc b), one_smul] at h3

variable {r k : ℕ}

theorem colFlag_eq (M : Matrix (Idx r k) (Idx r k) K) :
    ColFlag M ↔ FlagC M (fun b => Pi.single (pe (k := k) b) (1 : K)) := Iff.rfl

theorem rowFlag_eq (M : Matrix (Idx r k) (Idx r k) K) :
    RowFlag M ↔ FlagC Mᵀ (fun b => Pi.single (pf (k := k) b) (1 : K)) := Iff.rfl

theorem mem_sG_iff_flagC (g : GL (Idx r k) K) :
    g ∈ sG K r k ↔ FlagC (g : Matrix (Idx r k) (Idx r k) K) (fun b => Pi.single (pe (k := k) b) (1 : K)) ∧
      FlagC ((g⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K)ᵀ (fun b => Pi.single (pf (k := k) b) (1 : K)) := by
  rw [mem_sG_iff_flags, ← colFlag_eq, ← rowFlag_eq, colFlag_iff, rowFlag_iff]

end MassDataIdxStIm
