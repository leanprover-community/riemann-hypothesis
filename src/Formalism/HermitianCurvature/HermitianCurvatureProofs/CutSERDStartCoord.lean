module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterpolationInverseMatrixSumIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
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

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_start_coordinates : RDStartCoord := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  obtain ⟨-, -, hL, hQ, -⟩ := hD
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  have ht : ∀ Y (a b : Fin 2) l (i : Fin 6), Commute (X.t Y a b) (X.op l i) :=
    fun Y a b l i => Formalism.FourierDecayAlt.P.NFx1.TC.t_op_comm X Y a b l i
  intro Y a b l x hx
  have hm : Commute (X.QQ Y a b) x := by
    rw [Formalism.FourierDecayAlt.P.NFx3.QQ_apply]
    simp only [coordOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 0) (ht (star Y) b a l 3).neg_right
    · rw [hpb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 3) (ht (star Y) b a l 0).neg_right
    · rw [hc l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 1) (ht (star Y) b a l 4)
    · rw [hci l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 2) (ht (star Y) b a l 5)
    · rw [hcb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 4) (ht (star Y) b a l 1)
    · rw [hcbi l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 5) (ht (star Y) b a l 2)
  rw [hQ Y, Matrix.smul_apply]
  exact hm.smul_left _

end Formalism.FourierDecayAlt.P.CutSE
