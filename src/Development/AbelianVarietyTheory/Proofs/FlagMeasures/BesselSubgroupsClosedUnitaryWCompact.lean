module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem isClosedSub_of_closedSubgroup {k r : ℕ} {S : Set (Mat k r)} (hG : S ⊆ GG k r)
    (h : Formalism.FourierDecayAlt.B2.IsClosedSubgroup S) : IsClosedSub k r S :=
  ⟨hG, h.closed, h.one_mem, h.mul_mem, h.inv_mem⟩

theorem closedSub_groups : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    IsClosedSub k r (GG k r) ∧ IsClosedSub k r (Nset k r) ∧ IsClosedSub k r (UWset k r z) ∧
      IsClosedSub k r (Sset k r z) ∧ IsCompact (UWset k r z) := by
  intro k r z hz hT
  have cG : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (GG k r) := Formalism.FourierDecayAlt.P.B2x2.closedG k r
  have cN : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (Nset k r) := Formalism.FourierDecayAlt.P.B2x2.closedN k r
  have cW : Formalism.FourierDecayAlt.B2.IsClosedSubgroup (UWset k r z) := Formalism.FourierDecayAlt.P.B2x3.closedW k r z
  have sN : Nset k r ⊆ GG k r := fun g hg => hg.1
  have sW : UWset k r z ⊆ GG k r := fun g hg => hg.1
  have sS : Sset k r z ⊆ GG k r := by
    rintro s ⟨h, hh, n, hn, rfl⟩
    exact cG.mul_mem _ (sW hh) _ (sN hn)
  exact ⟨isClosedSub_of_closedSubgroup subset_rfl cG, isClosedSub_of_closedSubgroup sN cN,
    isClosedSub_of_closedSubgroup sW cW,
    isClosedSub_of_closedSubgroup sS (GlobalTheory.BesselPeriodCompare.closedS hz),
    Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hz hT⟩

end GlobalTheory.SgInf
