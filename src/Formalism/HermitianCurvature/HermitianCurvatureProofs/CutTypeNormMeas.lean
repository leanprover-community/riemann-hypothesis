module

public import Formalism.DoubleCosetMeasures.StatementZ
public import Formalism.HermitianCurvature.StatementTop
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

namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory Matrix

noncomputable section

def TypeComm : Prop :=
  ∀ (P : M.Par) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp)) (z e : Fin (2 * P.r + P.k + 1) → ℂ) (TP : Top.TypeProj P π z e),
    IsCRepOn (UWset P.k P.r z) π → ContinuousOn π (UWset P.k P.r z) →
    (∀ h ∈ UWset P.k P.r z, ∀ v, ‖π h v‖ = ‖v‖) →
    1 ≤ P.k → inWb P.k P.r z → 0 < Tz P.k P.r z → inWb P.k P.r e → herm (Hpk P.k P.r) e z = 0 →
    herm (Hpk P.k P.r) e e = 1 →
    ∀ g ∈ UWset P.k P.r z, ∀ l : ℂ, g *ᵥ e = l • e → ∀ ρ, (TP.E ρ).comp (π g) = (π g).comp (TP.E ρ)

def HouseMeas : Prop :=
  ∀ (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ), inWb k r z → (herm (Hpk k r) z z).re < 0 →
    inWb k r e → herm (Hpk k r) e z = 0 → herm (Hpk k r) e e = 1 →
    ∃ h : (Fin (2 * r + k + 1) → ℂ) → B.Mat k r, Measurable h ∧ (∀ u, h u ∈ UWset k r z) ∧
      ∀ u, inWb k r u → herm (Hpk k r) u z = 0 → u ≠ 0 → ∃ l : ℂ, h u *ᵥ u = l • e

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
