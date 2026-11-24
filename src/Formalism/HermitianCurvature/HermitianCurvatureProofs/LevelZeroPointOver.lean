module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Imports
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.StatementD
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def levelZeroPointOver {k r : ℕ} (a : C.LPt) (hle : D.ptSize a ≤ r) (g : B.Mat k (r - D.ptSize a)) : B.Mat k r :=
  D.castM (by omega) (U.mMap k (D.ptSize a) (r - D.ptSize a) (U.hMat (D.ptPerm a) (D.ptDiag a)) g)

def LeftFubini : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (T : D.LevTower k r Wp Wq),
    D.TowerNormalised T → ∀ (j : ℕ) (hj : j ≤ r), 1 ≤ j → ∀ (a : C.LPt) (ha : D.IsLocPt a j),
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X)
      (ℓ : X → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) (sx : X → B.Mat k r),
      (∀ x, sx x ∈ Sset k r T.base.z) ∧
      ∀ g ∈ JF.Om k (r - j) (T.bs j).z (T.bs j).z', ∀ H : B.Mat k r → (Wq →L[ℂ] Wp),
        ContinuousOn H {x | x ∈ B.GV k r ∧ Dmin k r T.base.z T.base.z' x ⟨j, by omega⟩ ≠ 0} →
        (∃ R : ℝ, ∀ x ∈ B.GV k r, H x ≠ 0 → B.gN x ≤ R) →
        Integrable (fun x => ℓ x (PBG.Kr T.base H (sx x * levelZeroPointOver a (by rw [ha.2]; exact hj)
          (D.castM (by rw [ha.2]) g)))) μ ∧
        B.JF (T.bs j) (D.castF (by rw [ha.2]) (D.sliceAt k r T.base.z T.base.z' H a)) g =
          ∫ x, ℓ x (PBG.Kr T.base H (sx x * levelZeroPointOver a (by rw [ha.2]; exact hj) (D.castM (by rw [ha.2]) g))) ∂μ

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
