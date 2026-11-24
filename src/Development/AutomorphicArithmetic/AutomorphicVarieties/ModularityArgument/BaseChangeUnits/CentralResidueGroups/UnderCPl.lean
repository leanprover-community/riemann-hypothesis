module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc

private theorem under_cPl {K : Type} [Field K] [NumberField K] [IsCMField K] (w : HeightOneSpectrum (𝓞 K)) :
    (cPl w).under (𝓞 ℚ) = w.under (𝓞 ℚ) := by
  have e : (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj K).toRingEquiv) :=
    (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  change x ∈ (cPl w).asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K)) ↔ x ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 K))
  have e2 : RingOfIntegers.mapRingEquiv (IsCMField.complexConj K).toRingEquiv (algebraMap (𝓞 ℚ) (𝓞 K) x) =
      algebraMap (𝓞 ℚ) (𝓞 K) x :=
    RingOfIntegers.ext (map_ratCast (IsCMField.complexConj K) (x : ℚ))
  rw [e, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, e2]
