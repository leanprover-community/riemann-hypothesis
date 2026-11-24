module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpanEqOneModOfSplitsInRayClassField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial


theorem _root_.GlobalTheory.T.exists_span_eq_one_mod_of_splits_in_rayClassField : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)),
    GlobalTheory.Mem.Fld.IsRayField K L 𝔮 → ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 →
      (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L →
        ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ 𝔮 := by
  first | exact @GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits | exact GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits | (intros; apply GlobalTheory.Mem.RaySplit.exists_span_eq_of_splits <;> assumption)
