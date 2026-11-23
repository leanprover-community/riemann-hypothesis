module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ImagQuadraticDescentGL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Z.Bc

def SplitBC {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (satE : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, normV w = normV (w.under (𝓞 F)) → ∃ B, sat (w.under (𝓞 F)) B ∧ satE w B

def DescS : Prop :=
  ∀ (M : Type) [Field M] [NumberField M], Module.finrank ℚ M = 2 → IsTotallyComplex M →
    ∀ sat' inf', IsCusp (F := M) 2 sat' inf' → RegInf 2 inf' → Gap2 inf' →
      (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) →
        ∃ B, sat' w B ∧ sat' w' B) →
      ∃ sat inf, IsCusp (F := ℚ) 2 sat inf ∧ SplitBC sat sat' ∧ ∀ τ m, inf' τ m → inf (τ.comp (algebraMap ℚ M)) m

end UpperTheory.V.Z.Bc
