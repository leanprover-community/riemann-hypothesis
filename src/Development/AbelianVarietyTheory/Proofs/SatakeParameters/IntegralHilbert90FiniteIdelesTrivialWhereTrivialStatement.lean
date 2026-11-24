module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Formalism.LocalToGlobal.Divisibility.TuplesLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.integral_h90_preimage_trivial_at_places_over_trivial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsConjOf σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ z ∈ U1 σ, z ∈ intU F E → ∃ x ∈ intU F E, h90 σ x = z ∧ ∀ P : HeightOneSpectrum (𝓞 E), (∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = P.under (𝓞 F) → GlobalTheory.Mem.Col2.afIso F E (z : AfE F E) P' = 1) → GlobalTheory.Mem.Col2.afIso F E (x : AfE F E) P = 1 := by
  first | exact @GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial | exact GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial | (intros; apply GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial <;> assumption)
