module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAffineOpenOfLocalSectionCombinationLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.isAffineOpen_of_local_sectionCombination_locus : ∀ (P Z : Scheme.{0}) (π : P ⟶ Z) [IsProper π] (J : Type) [Fintype J] (D : P.Opens) (W : Z.Opens), IsAffineOpen W → D ≤ π ⁻¹ᵁ W → (∀ z ∈ W, ∃ (W' : Z.Opens) (H : LB (π ⁻¹ᵁ W').toScheme) (σ : J → H.Sec) (m : J → Γ(Z, W ⊓ W')), z ∈ W' ∧ IsAffineOpen W' ∧ ⨆ k, nonzeroLocus (σ k) = ⊤ ∧ (∀ k, IsAffineOpen (nonzeroLocus (σ k))) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ (π ⁻¹ᵁ W').toScheme) (w : J → K), ⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι ≫ π) ⁻¹ᵁ W → Crd H σ y w → (⊤ ≤ (y ≫ (π ⁻¹ᵁ W').ι) ⁻¹ᵁ D ↔ ∑ k, valR (y ≫ (π ⁻¹ᵁ W').ι ≫ π) (W ⊓ W') (m k) * w k ≠ 0)) → IsAffineOpen D := by
  first | exact @GlobalTheory.ZH.CombLocus.isAffineOpen_of_comb | exact GlobalTheory.ZH.CombLocus.isAffineOpen_of_comb | (intros; apply GlobalTheory.ZH.CombLocus.isAffineOpen_of_comb <;> assumption)
