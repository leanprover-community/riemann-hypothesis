module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlace
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

theorem _root_.GlobalTheory.T.exists_unramified_totallyComplex_ext_with_unity_roots : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (g : ℕ)
    [Fact g.Prime] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (n : ℕ) (hn : 0 < n),
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsTotallyComplex E') (_ : Algebra E E')
      (_ : Algebra E' Ω) (_ : IsScalarTower E E' Ω) (_ : IsAlgClosure E' Ω) (w' : HeightOneSpectrum (𝓞 E'))
      (_ : IsPlaceOver A w'), ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal ∧ ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 ∧
      normV w' = g ^ n ∧ (∃ ζ : E', IsPrimitiveRoot ζ (g ^ n - 1)) ∧
      ∀ t ∈ Ine (F := E) A, ∀ e : E', t (algebraMap E' Ω e) = algebraMap E' Ω e := by
  first | exact @GlobalTheory.UnrCycExt.exists_unramified_ext | exact GlobalTheory.UnrCycExt.exists_unramified_ext | (intros; apply GlobalTheory.UnrCycExt.exists_unramified_ext <;> assumption)
