module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StabilizerFixesTailCoords
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
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem nilpotent_lie_finite_holds : LieNFin := by
  intro k r
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ (JfS.lieOf (Nset k r))
  have hfin : b.Finite := hli.setFinite
  have : Fintype b := hfin.fintype
  let Xs : Fin (Fintype.card b) → B.Mat k r := fun i => ((Fintype.equivFin b).symm i : B.Mat k r)
  have hrange : Set.range Xs = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin b).symm i).2
    · intro hx
      refine ⟨Fintype.equivFin b ⟨x, hx⟩, ?_⟩
      simp [Xs]
  refine ⟨Fintype.card b, Xs, fun i => hbS ((Fintype.equivFin b).symm i).2, fun X hX => ⟨?_, ?_⟩⟩
  · exact LieSplitPf.lieHpk_of (fun t => (hX t).1)
  · have hmem : X ∈ Submodule.span ℝ (Set.range Xs) := by
      rw [hrange, hspan]
      exact Submodule.subset_span hX
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    refine ⟨a, ?_⟩
    rw [← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext p q
    simp [Matrix.smul_apply, Complex.real_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
