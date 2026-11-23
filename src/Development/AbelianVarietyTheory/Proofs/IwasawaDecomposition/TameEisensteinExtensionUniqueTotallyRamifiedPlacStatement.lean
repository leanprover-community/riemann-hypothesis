module

public import Formalism.ConjugateSelfDual.Statement
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameEisensteinExtensionUniqueTotallyRamifiedPlac
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.tameEisensteinExtension_unique_totallyRamified_place : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (ϖ : 𝓞 E), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 →
    ∀ (π : Ω) [FiniteDimensional E (IntermediateField.adjoin E {π})] [NumberField (IntermediateField.adjoin E {π})],
    π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ W : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal ∧
      (∀ W' : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
        W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal → W' = W) ∧
      IsPlaceOver A W ∧ normV W = normV v ∧
      ∀ c : (W.adicCompletion (IntermediateField.adjoin E {π}))ˣ,
        (c : W.adicCompletion (IntermediateField.adjoin E {π})) =
          algebraMap (IntermediateField.adjoin E {π}) _ (IntermediateField.AdjoinSimple.gen E π) → IsUnifAt W c := by
  first | exact @GlobalTheory.TameRecPlace.main | exact GlobalTheory.TameRecPlace.main | (intros; apply GlobalTheory.TameRecPlace.main <;> assumption)
