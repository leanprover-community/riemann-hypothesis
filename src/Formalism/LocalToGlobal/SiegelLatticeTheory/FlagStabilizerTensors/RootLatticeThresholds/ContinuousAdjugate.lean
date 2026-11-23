module

public import Formalism.RealPlaceAnalysis.Complexify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix Topology

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier.JointQuot

section Pack

variable {n : ℕ} (ε : Fin n → Bool)

def mkUJ (y : Matrix (Fin n) (Fin n) ℂ) (hy : yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨y, Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε,
    mul_eq_one_comm.1 (by
      calc Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε * (yᴴ * Formalism.REAL.Jm ε * y) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]),
    by
      calc Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε * y = Formalism.REAL.Jm ε * (yᴴ * Formalism.REAL.Jm ε * y) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hy, Formalism.REAL.Jm_mul_self]⟩, hy⟩

end Pack

section Adj

variable {m : ℕ}

end Adj

end Formalism.L2.S.L6.UnitaryStandardVectors
