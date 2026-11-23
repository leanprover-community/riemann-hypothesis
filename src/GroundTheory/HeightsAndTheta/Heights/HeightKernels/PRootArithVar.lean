module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeightNE
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootArithmeticVariety

theorem isIntegral_of_pow_eq_one {x : ℂ} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) : IsIntegral ℤ x :=
  ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by
    simp [Polynomial.eval₂_sub, h]⟩

theorem isIntegral_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : ∀ a b, IsIntegral ℤ (M a b)) :
    IsIntegral ℤ M.det := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem (integralClosure ℤ ℂ) fun σ _ => ?_
  rw [Units.smul_def]
  refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun i _ => hM (σ i) i) _

theorem isIntegral_onePipe {j m : ℕ} (Z : Matrix (Fin j) (Fin m) ℂ) (hZ : ∀ a b, IsIntegral ℤ (Z a b))
    (a : Fin j) (b : Fin (j + m)) : IsIntegral ℤ (onePipe Z a b) := by
  simp only [onePipe, Matrix.of_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) b
  · rw [Fin.append_left, Matrix.one_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Fin.append_right]
    exact hZ a i

theorem isIntegral_rootCoord {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  refine isIntegral_det _ fun a b => ?_
  simp only [colsOf, Matrix.submatrix_apply, id]
  refine isIntegral_onePipe _ (fun a b => ?_) _ _
  obtain ⟨k, hk, h⟩ := hζ p.1 a b
  exact isIntegral_of_pow_eq_one hk h

end RootArithmeticVariety


open RootArithmeticVariety in
theorem RootArithVar.proof (h : CoordConeArithVar.Statement) : RootArithVar.Statement := by
  intro f j m ζ hf hζ
  have hK : Nonempty (Fin f) := ⟨⟨0, hf⟩⟩
  have := h (Fin f) (plBlocks f j m) ℂ (rootCoord ζ) (fun _ => plAnchor j m) 0 Fin.elim0 hK
    (fun k => by simp [rootCoord, anchor_minor]) (algebraicIndependent_empty_type)
    (fun i => Fin.elim0 i) ?_
  · simpa [rootPointIdeal] using this
  · rintro r ⟨p, rfl⟩
    have h1 : IsIntegral ℚ (rootCoord ζ p / rootCoord ζ ⟨p.1, plAnchor j m⟩) := by
      simp only [rootCoord, anchor_minor, div_one]
      exact (isIntegral_rootCoord ζ hζ p).tower_top
    exact (h1.tower_top (A := IntermediateField.adjoin ℚ (Set.range (Fin.elim0 : Fin 0 → ℂ)))).isAlgebraic

end

end GroundTheory.Heights₂.Heights
