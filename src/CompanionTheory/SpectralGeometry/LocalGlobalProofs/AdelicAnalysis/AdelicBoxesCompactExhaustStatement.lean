module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaust
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

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.adelic_boxes_compact_exhaust : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ (N : ℕ) (r : ℝ), 0 < N → IsCompact (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E))) ∧ (∀ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C → ∃ (N : ℕ) (r : ℝ), 0 < N ∧ 0 < r ∧ C ⊆ box b N r) ∧ ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (N : ℕ) (r x : ℝ) (X : Fin n → Fin M → AF F ⊗[F] E), ((τ (Multiplicative.ofAdd (x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X ∈ box b N (Real.exp x * r) ↔ X ∈ box b N r := by
  first | exact @GlobalTheory.CompanionTheory.SW.BoxF.box_facts | exact GlobalTheory.CompanionTheory.SW.BoxF.box_facts | (intros; apply GlobalTheory.CompanionTheory.SW.BoxF.box_facts <;> assumption)
