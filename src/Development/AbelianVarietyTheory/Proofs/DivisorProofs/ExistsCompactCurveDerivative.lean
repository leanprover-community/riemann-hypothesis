module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Tpr
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.WigCurve

theorem exists_unitary_matrix_curve (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E))
    (hZ : star Z = -Z) :
    ∃ f : ℝ → Matrix (Fin a) (Fin a) (Cinf E), (∀ t, f t ∈ unitary (Matrix (Fin a) (Fin a) (Cinf E))) ∧
      f 0 = 1 ∧ HasDerivAt (fun t => toL (f t)) (toL Z) 0 := by
  have hcs : ContinuousStar (Matrix (Fin a) (Fin a) (Cinf E)) := inferInstance
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin a) (Fin a) (Cinf E)) := NormedAlgebra.restrictScalars ℚ ℝ _
  refine ⟨fun t => NormedSpace.exp (t • Z), fun t => ?_, by simp, ?_⟩
  · refine @NormedSpace.exp_mem_unitary_of_mem_skewAdjoint _ _ _ _ _ ⟨hcs.continuous_star⟩ _ ?_
    rw [skewAdjoint.mem_iff, star_smul, hZ, star_trivial, smul_neg]
  · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
      LinearMap.toContinuousLinearMap
        { toFun := fun x => toL x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem exists_kinf_curve_tangent : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E)), star Z = -Z → ∃ c : ℝ → Kinf E a, c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).1) (toL Z) 0 := by
  intro E _ _ a Z hZ
  obtain ⟨f, hu, h0, hd⟩ := exists_unitary_matrix_curve E a Z hZ
  exact ⟨fun t => ⟨f t, hu t⟩, Subtype.ext h0, hd⟩

end GlobalTheory.WigCurve

end
