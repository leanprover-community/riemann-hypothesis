module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Formalism.PeriodIntegrals.QuotInv
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeil
public import Formalism.FormalDegreeBessel.FinalG
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
import Mathlib.Tactic.Linter.Style
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

namespace GlobalTheory.SgQuot

theorem isMatGroup_GG (k r : ℕ) : PI.IsMatGroup (GG k r) := by

  have hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := by
    have h := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact ⟨⟨_, _, h, (mul_comm _ _).trans h⟩, rfl⟩
  obtain ⟨h1, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ _ hH
  refine ⟨?_, h1, hmul, fun a ha => ⟨(hinv a ha).2, Matrix.mul_nonsing_inv a (hinv a ha).1⟩⟩

  show IsClosed {g : Mat k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem exists_isQuotMeas : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS : Measure (Mt k r)), IsClosedSub k r S →
    IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → ∃ ν : Measure (Mt k r), IsQuotMeas μG μS ν := by
  intro k r S μG μS hS hG hSμ hU
  obtain ⟨hSG, hcl, h1, hmul, hinv⟩ := hS

  have hSm : PI.IsMatGroup S :=
    ⟨hcl, h1, hmul, fun a ha => ⟨hinv a ha, ((isMatGroup_GG k r).2.2.2 a (hSG ha)).2⟩⟩

  exact GlobalTheory.QuotWeil.exists_isQuotM (2 * r + k + 1) (GG k r) S μG μS (isMatGroup_GG k r) hSm hSG hG hSμ hU.1

end GlobalTheory.SgQuot
