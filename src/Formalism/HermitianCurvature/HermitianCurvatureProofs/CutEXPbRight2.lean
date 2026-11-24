module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDiagonalMap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbRight

theorem castM_nset {k a b : ℕ} (e : a = b) {g : B.Mat k a} (hg : g ∈ Nset k a) : D.castM e g ∈ Nset k b := by
  subst e
  have : D.castM rfl g = g := by
    ext i j
    simp [D.castM]
  rw [this]
  exact hg

end Formalism.FourierDecayAlt.P.CutEXPbRight

namespace Formalism.FourierDecayAlt.P

open CutEX

private theorem castM_mul_eq_mul_castM {k a b : ℕ} (e : a = b) (g h : B.Mat k a) :
    D.castM e (g * h) = D.castM e g * D.castM e h := by
  subst e
  ext i j
  simp [D.castM]

theorem pullback_right_action : CutEX.PbRight := by
  intro Wp Wq _ _ _ _ _ _ P p G _ Z u μ hu
  have hm : D.castM (by omega) (U.muP P.k P.r (P.r - P.r) u) ∈ Nset P.k P.r :=
    CutEXPbRight.castM_nset _ (BigCellDiagonalMap.leviElement_nset u hu)
  unfold CutEX.pbTop CutEX.psiU PBQ.pbT CutEX.xT
  rw [← Ux4.mMap_mul_muP, castM_mul_eq_mul_castM]
  exact PBQ.pbF_right _ _ _ _ _ _ hm

end Formalism.FourierDecayAlt.P
