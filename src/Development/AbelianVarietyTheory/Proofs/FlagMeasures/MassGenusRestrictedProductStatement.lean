module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusRestrictedProduct
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

open GlobalTheory.HL
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.mass_genus_restricted_product : ∀ {ι : Type} (G : ι → Type) [∀ i, Group (G i)] (X : ι → Type) [∀ i, MulAction (G i) (X i)] (A : ∀ i, Subgroup (G i)) (H : Type) [Group H] (φ : H →* ∀ i, G i), Function.Injective φ → (∀ h, {i | φ h i ∉ A i}.Finite) → (∃ S : Finset (∀ i, G i), (∀ s ∈ S, {i | s i ∉ A i}.Finite) ∧ ∀ g : ∀ i, G i, {i | g i ∉ A i}.Finite → ∃ s ∈ S, ∃ h : H, ∃ k : ∀ i, G i, (∀ i, k i ∈ A i) ∧ g = φ h * s * k) → (∀ a : ∀ i, G i, {i | a i ∉ A i}.Finite → {h : H | ∀ i, (a i)⁻¹ * φ h i * a i ∈ A i}.Finite) → ∀ x0 : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (A i) ≠ 0 ∧ (A i).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | A i ≠ MulAction.stabilizer (G i) (x0 i)}.Finite → ∃ V1 : ℝ, 0 < V1 ∧ ∀ x : ∀ i, X i, (∀ i, (MulAction.stabilizer (G i) (x0 i)).relIndex (MulAction.stabilizer (G i) (x i)) ≠ 0 ∧ (MulAction.stabilizer (G i) (x i)).relIndex (MulAction.stabilizer (G i) (x0 i)) ≠ 0) → {i | x i ≠ x0 i}.Finite → (∑' o : Quot (fun y y' : (∀ i, X i) => ∃ h : H, φ h • y = y'), if (∀ i, ∃ g : G i, g • x i = o.out i) ∧ {i | o.out i ≠ x i}.Finite then (({h : H | φ h • o.out = o.out}.encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V1 * ∏ᶠ i, invVol (MulAction.stabilizer (G i) (x0 i)) (MulAction.stabilizer (G i) (x i))) := by
  first | exact @GlobalTheory.HL.mass_restricted_product | exact GlobalTheory.HL.mass_restricted_product | (intros; apply GlobalTheory.HL.mass_restricted_product <;> assumption)
