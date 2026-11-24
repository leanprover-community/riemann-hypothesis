module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLaws
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

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.rec_unique_of_laws : LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w.adicCompletion E) → WD h) (ψ : AddChar (w.adicCompletion E) Circle) (e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ), Continuous ψ → ψ ≠ 1 → e ψ = e' ψ → LawsMin a ha e rc → LawsMin a ha e' rc' → rc = rc' := by
  first | exact @GlobalTheory.LocLanglands.Unique.eq_of_lawsMin | exact GlobalTheory.LocLanglands.Unique.eq_of_lawsMin | (intros; apply GlobalTheory.LocLanglands.Unique.eq_of_lawsMin <;> assumption)
