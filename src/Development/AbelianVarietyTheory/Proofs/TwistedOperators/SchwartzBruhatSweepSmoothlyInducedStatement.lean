module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatSweepSmoothlyInduced
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

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

theorem _root_.GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  first | exact @GlobalTheory.SBInduced.sb_induced | exact GlobalTheory.SBInduced.sb_induced | (intros; apply GlobalTheory.SBInduced.sb_induced <;> assumption)
