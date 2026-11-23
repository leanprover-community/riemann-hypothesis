module

public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideOfGoodLocalData
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.amplitude_one_side_of_good_local_data : ∀ (D : D7) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (θ : ℝ) (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), 0 < D.host.v → 0 < θ → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → OneSide W.z W.π (psiS D W.z) W.μG W.μW (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS A.Φ A.cN ∧ OneSide W.z' W.π' (psiS D W.z') W.μG W.μW' (ENNReal.ofReal ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • lebN D.R.k D.R.rS) W.νS' A.Φ' A.cN := by
  first | exact @GlobalTheory.AmpSides.oneSide_of_good | exact GlobalTheory.AmpSides.oneSide_of_good | (intros; apply GlobalTheory.AmpSides.oneSide_of_good <;> assumption)
