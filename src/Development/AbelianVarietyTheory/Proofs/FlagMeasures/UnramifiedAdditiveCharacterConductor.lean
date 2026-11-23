module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocalDensityValue

def placeHom (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Fv F v →+ AF F :=
  (AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom

theorem continuous_placeHom (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (placeHom F v) :=
  Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v)

def localChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (placeHom F v)

theorem isLocalChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) (v : HeightOneSpectrum (𝓞 F)) (m : ℤ)
    (hm : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.IsLocalChar F v (localChar F ψ v) := by
  refine ⟨hψ.1.comp (continuous_placeHom F v), fun t => hψ.2.1 _, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (m + 1))
  have := (hm t).1 fun s _ => h _
  rw [ht, WithZero.exp_le_exp] at this
  omega

end GlobalTheory.LocalDensityValue
