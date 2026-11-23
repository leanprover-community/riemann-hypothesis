module

public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgEquivariant
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmgUW

lemma one_mem_UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z := by
  simp [UWset, UH]

theorem omg_left_right : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → ∀ g ∈ B.GV k r, (∀ h ∈ UWset k r z, GlobalTheory.WigSh.omg k r z z' (h * g) = GlobalTheory.WigSh.omg k r z z' (g)) ∧ ∀ h' ∈ UWset k r z', GlobalTheory.WigSh.omg k r z z' (g * h') = h'⁻¹ *ᵥ GlobalTheory.WigSh.omg k r z z' (g) := by
  intro k r z z' hz hTz hz' hTz' g hg
  refine ⟨fun h hh => ?_, fun h' hh' => ?_⟩
  · have hhU : h ∈ UH (Hpk k r) := by
      simp only [UWset, Set.mem_setOf_eq] at hh
      exact hh.1
    have hii : h⁻¹⁻¹ = h :=
      Matrix.nonsing_inv_nonsing_inv h
        (Matrix.isUnit_det_of_right_inverse (GlobalTheory.WigSh.OmgEquiv.mul_inv hhU))
    have e := GlobalTheory.WigSh.omg_equivariant k r z z' g h⁻¹ 1 hz hTz hz' hTz' hg
      (GlobalTheory.WigSh.OmgEquiv.inv_mem hh) (one_mem_UWset k r z')
    rw [hii, mul_one, inv_one, Matrix.one_mulVec] at e
    exact e
  · have e := GlobalTheory.WigSh.omg_equivariant k r z z' g 1 h' hz hTz hz' hTz' hg
      (one_mem_UWset k r z) hh'
    rw [inv_one, one_mul] at e
    exact e

end GlobalTheory.CompanionTheory.OmgUW
