module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeExpansionOverFinitePlaces
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

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.amplitude_expansion_over_finite_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ S1 : Finset (HeightOneSpectrum (𝓞 F)), G.Om ⊆ S1 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ Q : Prop → Prop, G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = κ * ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty), ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ) else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
  first | exact @GlobalTheory.HL.DefectPhase.amp_sum_defect_sets | exact GlobalTheory.HL.DefectPhase.amp_sum_defect_sets | (intros; apply GlobalTheory.HL.DefectPhase.amp_sum_defect_sets <;> assumption)
