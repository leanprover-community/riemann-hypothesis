module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantImageOpenClosedLocalSections
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

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.invariant_image_openClosed_local_sections : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (a₀ : Inv r F), Delta a₀ ≠ 0 → ((¬ ∃ X : Hn r F E, HasInv X a₀) → ∀ᶠ a in 𝓝 a₀, ¬ ∃ X : Hn r F E, HasInv X a) ∧ ((∃ X : Hn r F E, HasInv X a₀) → ∃ (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ ContinuousOn s Ω ∧ (∀ a ∈ Ω, Delta a ≠ 0 ∧ HasInv (s a) a) ∧ ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C}) := by
  first | exact @GlobalTheory.JR.image_openClosed_section | exact GlobalTheory.JR.image_openClosed_section | (intros; apply GlobalTheory.JR.image_openClosed_section <;> assumption)
