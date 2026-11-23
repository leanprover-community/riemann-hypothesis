module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

theorem group_vector_space : GVGrp := by
  intro k r
  refine ⟨⟨⟨1 + 1, (1 / 2 : ℂ) • 1, ?_, ?_⟩, rfl⟩, fun g₀ hg₀ => ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_one, smul_add, ← add_smul]
    norm_num
  · rw [Matrix.smul_mul, Matrix.one_mul, smul_add, ← add_smul]
    norm_num
  · have hdet : IsUnit g₀.det := Formalism.FourierDecayAlt.P.PBG.isUnit_det_of_UH hg₀
    refine ⟨Matrix.nonsing_inv_mul g₀ hdet, fun h hh => ⟨Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul hg₀ hh,
      Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (Formalism.FourierDecayAlt.P.PBM.GV_inv_mem g₀ hg₀) hh, ?_⟩⟩
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g₀ hdet, Matrix.one_mul]

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
