module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.TwistBlockK

theorem atK_sub_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (g : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
  At (evFin F v) (g - 1) → At (evFin F v) Y → At (evFin F v) ((⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ + (g).toBlocks₂₁ + (g).toBlocks₂₂) +
      Y * (⅟(2 : AF F) • ((g).toBlocks₁₁ + (g).toBlocks₁₂ - (g).toBlocks₂₁ - (g).toBlocks₂₂))) - 1) := by
  intro F E _ _ _ _ _ d v g Y hg hY u hu
  have hgu := hg u hu
  have hYu : u • Y = 0 := hY u hu
  rw [smul_sub, sub_eq_zero] at hgu
  have h11 : u • g.toBlocks₁₁ = u • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using this
  have h22 : u • g.toBlocks₂₂ = u • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inr i)) (Sum.inr j)
    simpa [Matrix.toBlocks₂₂, Matrix.one_apply] using this
  have h12 : u • g.toBlocks₁₂ = 0 := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.toBlocks₁₂, Matrix.one_apply] using this
  have h21 : u • g.toBlocks₂₁ = 0 := by
    ext i j
    have := congrFun (congrFun hgu (Sum.inr i)) (Sum.inl j)
    simpa [Matrix.toBlocks₂₁, Matrix.one_apply] using this
  rw [smul_sub, smul_add, ← Matrix.smul_mul, hYu, Matrix.zero_mul, add_zero,
    smul_comm u (⅟(2 : AF F))]
  simp only [smul_add, h11, h12, h21, h22, add_zero]
  rw [← add_smul, invOf_two_add_invOf_two, one_smul, sub_self]

end GlobalTheory.TwistBlockK
