module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FundamentalSetMeasureCommensurableIndexRatio
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.fundamental_set_measure_commensurable_index_ratio : ∀ (G α : Type) [Group G] [MulAction G α] [MeasurableSpace α] (μ : Measure α) (R : Set α) (A B : Subgroup G) (Ω K : Set α), (∀ s : G, Measurable fun x : α => s • x) → Countable A → Countable B → μ Rᶜ = 0 → (∀ s ∈ A ⊔ B, (∀ x ∈ R, s • x ∈ R) ∧ μ.map (fun x => s • x) = μ) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → MeasurableSet Ω → MeasurableSet K → (∀ x ∈ R, ∃! s, s ∈ A ∧ s • x ∈ Ω) → (∀ x ∈ R, ∃! s, s ∈ B ∧ s • x ∈ K) → μ K = ENNReal.ofReal (GlobalTheory.HL.invVol A B) * μ Ω := by
  first | exact @GlobalTheory.CovolIdx.measure_eq_invVol_mul | exact GlobalTheory.CovolIdx.measure_eq_invVol_mul | (intros; apply GlobalTheory.CovolIdx.measure_eq_invVol_mul <;> assumption)
