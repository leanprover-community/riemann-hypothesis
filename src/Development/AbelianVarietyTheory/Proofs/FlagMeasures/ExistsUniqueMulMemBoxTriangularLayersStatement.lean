module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Data.Fintype.Defs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueMulMemBoxTriangularLayers
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.T.existsUnique_mul_mem_box_triangular_layers : ∀ (M I A B D : Type) [Monoid M] [Fintype I] [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] (ht : I → ℕ) (C : (I → A) × B × D → M) (Γ : Set M) (Λ₁ F₁ : I → Set A) (Λ₂ F₂ : Set B) (Λ₃ F₃ : Set D), Function.Injective C → C 0 = 1 → (∀ p q, ∃ w, C p * C q = C w ∧ (∀ i, (∀ l, ht l < ht i → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2)) → Γ ⊆ Set.range C → (1 : M) ∈ Γ → (∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) → (∀ a ∈ Γ, ∃ b ∈ Γ, b * a = 1) → (∀ p, C p ∈ Γ → ∀ i, p.1 i ∈ Λ₁ i) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 ∈ Λ₂) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 = 0 → p.2.2 ∈ Λ₃) → (∀ i, ∀ a ∈ Λ₁ i, ∃ p, C p ∈ Γ ∧ p.1 = Pi.single i a) → (∀ b ∈ Λ₂, ∃ p, C p ∈ Γ ∧ p.1 = 0 ∧ p.2.1 = b) → (∀ d ∈ Λ₃, C (0, 0, d) ∈ Γ) → (∀ i a, ∃! b, b ∈ Λ₁ i ∧ b + a ∈ F₁ i) → (∀ a, ∃! b, b ∈ Λ₂ ∧ b + a ∈ F₂) → (∀ a, ∃! b, b ∈ Λ₃ ∧ b + a ∈ F₃) → ∀ q, ∃! m, m ∈ Γ ∧ m * C q ∈ C '' (Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃) := by
  first | exact @GlobalTheory.DegVol.RefCov.existsUnique_mul_mem_box_of_layers | exact GlobalTheory.DegVol.RefCov.existsUnique_mul_mem_box_of_layers | (intros; apply GlobalTheory.DegVol.RefCov.existsUnique_mul_mem_box_of_layers <;> assumption)
