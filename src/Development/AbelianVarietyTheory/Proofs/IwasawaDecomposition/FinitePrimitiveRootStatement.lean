module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePrimitiveRoot
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.finite_primitive_root_of_clC_le : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ) (h : clC l (Kt l K₀ L) ≤ clC l (Kt l K₀ L ⊔ muK l k)), letI := (Subring.inclusion h).toAlgebra; Module.Finite ↥(clC l (Kt l K₀ L)) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ ∃ z : (↥(clC l (Kt l K₀ L ⊔ muK l k)))ˣ, IsPrimitiveRoot (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) (l ^ k) ∧ ∀ x : FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), ∃ p : Polynomial ↥(clC l (Kt l K₀ L)), ∃ d : ↥(clC l (Kt l K₀ L)), d ≠ 0 ∧ x * algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (algebraMap _ ↥(clC l (Kt l K₀ L ⊔ muK l k)) d) = algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (Polynomial.aeval (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) p) := by
  first | exact @GlobalTheory.CycLayers.finite_primitive_root | exact GlobalTheory.CycLayers.finite_primitive_root | (intros; apply GlobalTheory.CycLayers.finite_primitive_root <;> assumption)
