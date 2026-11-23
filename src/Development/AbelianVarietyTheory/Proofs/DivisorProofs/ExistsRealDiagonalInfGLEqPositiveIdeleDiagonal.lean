module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic
  GroundTheory.Automorphic.Reduction

namespace GlobalTheory.SiegelTorusInf

theorem exists_diag_infGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ d : GL (Fin a) (Cinf E), d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) ∧
      diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) = infGL E a d := by
  have h0 : ∀ i, (r i : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (hr i).ne'
  refine ⟨⟨Matrix.diagonal (fun i => fun _ => (r i : ℂ)), Matrix.diagonal (fun i => fun _ => (r i : ℂ)⁻¹), ?_, ?_⟩,
    rfl, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    exact mul_inv_cancel₀ (h0 i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    exact inv_mul_cancel₀ (h0 i)
  · have key : ∀ i, ((posIdele (K := E) (r i) (hr i) : IdeleGroup E) : Ad E) =
        1 - sInf E 1 + sInf E (fun _ => (r i : ℂ)) := fun i => by
      rw [GlobalTheory.CuspBoundSiegel.posIdele_congr (hr i) (Real.exp_pos _) (Real.exp_log (hr i)).symm,
        GlobalTheory.CuspBoundSiegel.posIdele_exp]
      change 1 - sInf E 1 + sInf E _ = _
      congr 2
      funext w
      change Complex.exp (Real.log (r i) : ℂ) = (r i : ℂ)
      rw [← Complex.ofReal_exp, Real.exp_log (hr i)]
    refine Units.ext ?_
    rw [coe_diagUnits]
    refine Matrix.ext fun i j => ?_
    change _ = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
      sInf E (Matrix.diagonal (fun i => (fun _ => (r i : ℂ) : Cinf E)) i j)
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq]
      exact key i
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, Matrix.one_apply_ne h,
        map_zero, sub_zero, add_zero]

end GlobalTheory.SiegelTorusInf

end
