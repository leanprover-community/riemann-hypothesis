module

public import Formalism.HermitianLattices.StatementMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardUnimodularGluingsTwoLinesLe
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.card_unimodular_gluings_two_lines_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (β₁ β₂ : E) (N₁ N₂ : Submodule (𝓞 E) E) (𝔫 : Ideal (𝓞 E)), star β₁ = β₁ → star β₂ = β₂ → β₁ ≠ 0 → β₂ ≠ 0 → Submodule.IsLattice E N₁ → Submodule.IsLattice E N₂ → Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 → ENat.card {M : Submodule (𝓞 E) (Fin 2 → E) // Submodule.IsLattice E M ∧ (∀ x, x ∈ M ↔ ∀ y ∈ M, star y ⬝ᵥ ((Matrix.diagonal ![β₁, β₂]) *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧ (∀ t, t ∈ N₁ ↔ ![t, 0] ∈ M) ∧ ∀ t, t ∈ N₂ ↔ ![0, t] ∈ M} ≤ (Ideal.absNorm 𝔫 : ENat) := by
  first | exact @GlobalTheory.GlueLines.card_gluings_le | exact GlobalTheory.GlueLines.card_gluings_le | (intros; apply GlobalTheory.GlueLines.card_gluings_le <;> assumption)
