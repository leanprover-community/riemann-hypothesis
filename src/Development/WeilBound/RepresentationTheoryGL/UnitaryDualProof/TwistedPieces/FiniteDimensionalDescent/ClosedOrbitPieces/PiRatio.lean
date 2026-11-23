module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.PieceGood
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PsiMulVec
public import GroundTheory.Brauer.DoubleCentralizer
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FeIsField

@[expose] public section

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem pi_ratio {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {e : Matrix (Fin N) (Fin N) k} (he : e ∈ A) (hid : IsIdempotentElem e) (hne : e ≠ 0)
    (hf : ∀ a ∈ A, e * a = 0 ∨ ∃ b ∈ A, e * a * b = e) :
    0 < Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) ∧
      Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) ∣ e.rank ∧
      Module.finrank k ((cenSub A).map (LinearMap.mulLeft k e)) =
        (e.rank / Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e))) ^ 2 *
          Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) := by
  classical
  let _ : Field (Fe hA he) := (Fe_isField hA he hne hf).toField
  have hFd : Module.finrank k (Fe hA he) = Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) := by
    rw [← map_Th_Fe hA he, ← (Submodule.equivMapOfInjective (Th e) Th_inj _).finrank_eq,
      Subalgebra.finrank_toSubmodule]
  have hD : Module.finrank k ((cenSub A).map (LinearMap.mulLeft k e)) =
      Module.finrank k (Module.End (Fe hA he) (Wd e)) := by
    unfold cenSub
    rw [← range_Psi hA he hid, LinearMap.finrank_range_of_inj (Psi_inj hA he)]
  set_option synthInstance.maxHeartbeats 200000 in
  have h1 := GroundTheory.Brauer.finrank_mul_finrank_end k (Fe hA he) (Wd e)
  have h2 := Module.finrank_mul_finrank k (Fe hA he) (Wd e)
  have hr : e.rank = Module.finrank k (Wd e) := (Matrix.finrank_range_mulVecLin e).symm
  have hd0 : 0 < Module.finrank k (Fe hA he) := Module.finrank_pos
  rw [← hFd, hD, hr]
  set d := Module.finrank k (Fe hA he)
  set m := Module.finrank (Fe hA he) (Wd e)
  rw [← h2] at h1 ⊢
  refine ⟨hd0, dvd_mul_right _ _, ?_⟩
  rw [Nat.mul_div_cancel_left m hd0]
  apply Nat.eq_of_mul_eq_mul_left hd0
  rw [h1]; ring

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
