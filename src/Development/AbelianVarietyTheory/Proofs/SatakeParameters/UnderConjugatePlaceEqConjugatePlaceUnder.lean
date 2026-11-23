module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.ConjUnder

theorem complexConj_algebraMap {K M : Type} [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (x : K) :
    IsCMField.complexConj M (algebraMap K M x) = algebraMap K M (IsCMField.complexConj K x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K M)) x).symm

theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (UpperTheory.V.Af.Bc.cPl w).asIdeal =
      w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

theorem cPl_under : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (w : HeightOneSpectrum (𝓞 M)),
    (UpperTheory.V.Af.Bc.cPl w).under (𝓞 K) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K)) := by
  intro K M _ _ _ _ _ _ _ w
  apply HeightOneSpectrum.ext
  rw [cPl_asIdeal]
  change (UpperTheory.V.Af.Bc.cPl w).asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M))).comap _
  rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  ext x
  exact complexConj_algebraMap (x : K)

end GlobalTheory.ConjUnder
