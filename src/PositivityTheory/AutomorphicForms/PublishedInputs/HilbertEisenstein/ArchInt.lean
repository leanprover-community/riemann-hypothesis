module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs
public import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
public import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import GroundTheory.LocalFields.LocalZetaShell
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def rc (a : (InfiniteAdeleRing F)ˣ) (v : InfinitePlace F) : ℝ :=
  (UpperTheory.V.TR.infEq F).symm (a : InfiniteAdeleRing F) v

def archK (y : (UpperTheory.V.TR.Rinf F)ˣ) (ξ : F) (a : (InfiniteAdeleRing F)ˣ) : ℂ :=
  ∏ v, ((((rc a v * y.val v + (rc a v)⁻¹ * reAt v ξ : ℝ)) : ℂ) *
    Complex.exp (-(Real.pi : ℂ) * (((rc a v * y.val v) ^ 2 + ((rc a v)⁻¹ * reAt v ξ) ^ 2 : ℝ) : ℂ)))

def ωI (ω : HChar F) (a : (InfiniteAdeleRing F)ˣ) : ℂ := ((ω.1 (ofInfinite a) : ℂˣ) : ℂ)

def chiW (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (w : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4

def ArchInt : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ ξ : Fˣ,
    Integrable (fun a => archK y (ξ : F) a * (ωI ω a)⁻¹) (infiniteIdeleMeasure F) ∧
      ∫ a, archK y (ξ : F) a * (ωI ω a)⁻¹ ∂infiniteIdeleMeasure F =
        if ∀ v, 0 < reAt v (ξ : F) then (2 : ℂ) ^ Fintype.card (InfinitePlace F) *
          Complex.exp (-(2 * Real.pi : ℂ) * ∑ v, (reAt v (ξ : F) : ℂ) * (y.val v : ℂ)) else 0

def CoefDiv : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ) (z : Af F) (m : HeightOneSpectrum (𝓞 F) → ℤ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w, Valued.v (pLoc F w z) = WithZero.exp (dd w - m w)) → (∀ w ∉ S, m w = 0) →
    coefAt (divS ω c) z =
      if ∀ w ∈ S, 0 ≤ m w then ∏ w ∈ S, ∑ j ∈ Finset.range ((m w).toNat + 1), chiW ω c w ^ j else 0

def LocRam : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ w : HeightOneSpectrum (𝓞 F), c w ≠ 0 →
    (∀ k : ℤ, -((c w : ℤ) + dd w) < k →
      ∫ x in ordShell (w.adicCompletion F) k, ((ω.loc w x : ℂˣ) : ℂ) *
        (localAdelicChar F w (x : w.adicCompletion F) : ℂ) ∂multHaar (w.adicCompletion F) = 0) ∧
    ∫ x in ordShell (w.adicCompletion F) (-((c w : ℤ) + dd w)), ((ω.loc w x : ℂˣ) : ℂ) *
        (localAdelicChar F w (x : w.adicCompletion F) : ℂ) ∂multHaar (w.adicCompletion F) ≠ 0

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
