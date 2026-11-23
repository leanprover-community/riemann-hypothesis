module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependent
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
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.valuationSubring_le_of_residue_independent : ∀ {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic → (∀ i j, (Φ.coeff i).coeff j ∈ V) → Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 → (∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω) → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → (∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W₁.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits) → W₁ ≤ W₂ := by
  first | exact @GlobalTheory.BertiniNoether.le_of_residue_independent | exact GlobalTheory.BertiniNoether.le_of_residue_independent | (intros; apply GlobalTheory.BertiniNoether.le_of_residue_independent <;> assumption)
