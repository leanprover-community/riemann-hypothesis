module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicUnramifiedCompletedIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.exists_cyclotomic_unramified_completed_integers : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ), ∃ _ : IsDiscreteValuationRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), IsAlgClosed (IsLocalRing.ResidueField ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ (∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∀ y ∈ clC l (Kt l K₀ L ⊔ muK l k), ‖x‖ ≤ ‖y‖ → x / y ∈ clC l (Kt l K₀ L ⊔ muK l k)) ∧ muK l 0 = ⊥ ∧ (∃ T : Finset ℂ_[l], ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ Submodule.span ↥(clC l (Kt l K₀ L)) (T : Set ℂ_[l])) ∧ ∃ ζ ∈ clC l (Kt l K₀ L ⊔ muK l k), IsPrimitiveRoot ζ (l ^ k) ∧ ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ (p : Polynomial ↥(clC l (Kt l K₀ L))) (d : ↥(clC l (Kt l K₀ L))), d ≠ 0 ∧ x * (d : ℂ_[l]) = Polynomial.aeval ζ p := by
  first | exact @GlobalTheory.CycClosure.exists_cyclotomic_integers | exact GlobalTheory.CycClosure.exists_cyclotomic_integers | (intros; apply GlobalTheory.CycClosure.exists_cyclotomic_integers <;> assumption)
