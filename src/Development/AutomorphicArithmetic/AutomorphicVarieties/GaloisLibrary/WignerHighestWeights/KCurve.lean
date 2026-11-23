module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.kCurve :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E)), star Z = -Z →
      ∃ k : ℝ → Kinf E a, k 0 = 1 ∧ HasDerivAt (fun t => toL (k t).1) (toL Z) 0 := by
  intro E _ _ _ a Z hZ
  open scoped Matrix.Norms.Operator in
  have hs : ∀ t : ℝ, star (NormedSpace.exp (t • Z)) = NormedSpace.exp (-(t • Z)) := fun t => by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, ← Matrix.star_eq_conjTranspose, star_smul,
      star_trivial, hZ, smul_neg]
  have hm : ∀ t : ℝ, NormedSpace.exp (t • Z) ∈ unitary (Matrix (Fin a) (Fin a) (Cinf E)) := fun t => by
    rw [Unitary.mem_iff, hs, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
    simp
  refine ⟨fun t => ⟨NormedSpace.exp (t • Z), hm t⟩, Subtype.ext (by simp), ?_⟩
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h
