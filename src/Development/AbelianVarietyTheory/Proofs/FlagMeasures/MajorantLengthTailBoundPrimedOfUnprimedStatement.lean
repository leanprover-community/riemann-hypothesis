module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTailBoundPrimedOfUnprimed
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.majorantLengthTailBound_primed_of_unprimed : ∀ (D : D7) (τ : D.what₂.Tau) (w : D.what₂.Word) (θ : ℝ) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (q : ℕ) (H₁ : ℝ), (∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z W.νS A.Φ q H₁) → ∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z' W.νS' A.Φ' q H₁ := by
  first | exact @GlobalTheory.TypeAsm.tailBd_primed_of_unprimed | exact GlobalTheory.TypeAsm.tailBd_primed_of_unprimed | (intros; apply GlobalTheory.TypeAsm.tailBd_primed_of_unprimed <;> assumption)
