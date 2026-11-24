module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nearOne_glEmbMat_iff (s : kˣ) (m : ℕ) (A : Matrix (Fin m) (Fin m) k) :
    NearOne s (glEmbMat k m A) ↔ NearOne s A := by
  have e1 : ∀ a b : Fin m, glEmbMat k m A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
    intro a b
    simp [glEmbMat]
  have e2 : ∀ a b : Fin m, (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (1 : Matrix (Fin m) (Fin m) k) a b := by
    intro a b
    simp [Matrix.one_apply, Fin.castSucc_inj]
  have z : (0 : k) ∈ (ballSub s : Set k) := (ballSub s).zero_mem
  constructor
  · intro h a b
    have h1 := h (Fin.castSucc a) (Fin.castSucc b)
    rwa [e1, e2] at h1
  · intro h a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        have e : glEmbMat k m A (Fin.last m) (Fin.last m) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) (Fin.last m) = 0 := by
          simp [glEmbMat]
        rw [e]
        exact z
      | cast j =>
        have e : glEmbMat k m A (Fin.last m) (Fin.castSucc j) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) (Fin.castSucc j) = 0 := by
          rw [Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne', sub_zero]
          simp [glEmbMat]
        rw [e]
        exact z
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        have e : glEmbMat k m A (Fin.castSucc i) (Fin.last m) - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.castSucc i) (Fin.last m) = 0 := by
          rw [Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne, sub_zero]
          simp [glEmbMat]
        rw [e]
        exact z
      | cast j =>
        rw [e1, e2]
        exact h i j

theorem sEmb_mem_congM_iff (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (x : Mir k n) :
    sEmb k n x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs (n + 1) ↔ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n := by
  have e1 : (((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      glEmbMat k (n + 1) ((x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := rfl
  have e2 : ((((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ : GL (Fin (n + 1 + 1)) k) :
        Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      glEmbMat k (n + 1) (((x : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    have : ((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ = ((sEmb k n x⁻¹ : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) := by
      rw [map_inv]; rfl
    rw [this]
    rfl
  show (NearOne s (((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) ∧
        NearOne s ((((sEmb k n x : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k)⁻¹ : GL (Fin (n + 1 + 1)) k) :
          Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)) ↔
      (NearOne s ((x : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∧
        NearOne s (((x : GL (Fin (n + 1)) k)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k))
  rw [e1, e2, nearOne_glEmbMat_iff, nearOne_glEmbMat_iff]

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
