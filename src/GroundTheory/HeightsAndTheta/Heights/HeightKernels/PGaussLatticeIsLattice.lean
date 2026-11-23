module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGauss
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace PGaussLatticeIsLattice

def colBasis {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    Module.Basis (Fin g) ℝ (EuclideanSpace ℝ (Fin g)) :=
  (Pi.basisFun ℝ (Fin g)).map
    ((B.toLinearEquiv' (B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hB))).trans
      (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm)

theorem colBasis_apply {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) (i : Fin g) :
    colBasis B hB i = WithLp.toLp 2 (B *ᵥ Pi.single i 1) := by
  rw [colBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  rfl

theorem gaussLattice_eq_span {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    gaussLattice B = Submodule.span ℤ (Set.range (colBasis B hB)) := by
  unfold gaussLattice
  congr 2
  funext i
  exact (colBasis_apply B hB i).symm

end PGaussLatticeIsLattice


open PGaussLatticeIsLattice in
theorem GaussLatticeIsLattice.proof : GaussLatticeIsLattice.Statement := by
  intro g B hB
  have h := gaussLattice_eq_span B hB
  refine ⟨?_, fun {_} => ⟨?_⟩⟩
  · rw [h]; infer_instance
  · rw [h]; exact ZSpan.span_top (colBasis B hB)

end

end GroundTheory.Heights₂.Heights
