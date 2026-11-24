module

public import Formalism.UnipotentAdelicQuotients.WeylLatDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

abbrev IncreasingRowChoicePerColumn (N : ℕ) (Y : YoungDiagram) : Type := ∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N

def sig {Lt : Type} (N : ℕ) (s : Lt) : Fin N × Fin N → Lt × ℕ × Fin N := fun v => (s, (v.2 : ℕ), v.1)

theorem map_nablaX {Lt : Type} [Fintype Lt] (K : Type) [CommRing K] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (J : WeylLatticeDuality.ColChoice N nu) :
    map (Int.castRingHom K) (WeylLatticeDuality.nablaX N nu J) =
      ∏ s, rename (sig N s) (GlobalTheory.WeylMinorDual.colProd K N (nu s) (hY s) (J s)) := by
  unfold WeylLatticeDuality.nablaX GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 p q
  simp [sig]

theorem colLen_le_of_rowLen {N : ℕ} {Y : YoungDiagram} (h : Y.rowLen N = 0) : Y.colLen 0 ≤ N := by
  by_contra hc'
  have hc := not_le.mp hc'
  have h1 : (N, 0) ∈ Y := YoungDiagram.mem_iff_lt_colLen.mpr hc
  have h2 := YoungDiagram.mem_iff_lt_rowLen.mp h1
  omega

end GlobalTheory.WeylLatDualProof
