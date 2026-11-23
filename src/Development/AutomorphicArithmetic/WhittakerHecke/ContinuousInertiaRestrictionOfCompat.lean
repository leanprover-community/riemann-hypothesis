module

public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

theorem UpperTheory.continuous_inertia_restriction_of_compat :
    ∀ {E L Ω : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Field Ω] [Algebra E L] [Algebra E Ω] [Algebra L Ω]
        [IsScalarTower E L Ω] (A : ValuationSubring Ω) (ι : Ine (F := E) A →* Ine (F := L) A),
        (∀ (t : Ine (F := E) A) (x : Ω), (ι t : G L Ω) x = (t : G E Ω) x) → Continuous ι := by
  intro E L Ω _ _ _ _ _ _ _ _ _ A ι hι
  haveI : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite ℚ E L
  apply continuous_of_continuousAt_one ι
  rw [ContinuousAt, map_one, tendsto_subtype_rng, Filter.tendsto_def]
  intro s hs
  rw [OneMemClass.coe_one] at hs
  obtain ⟨K, hK, hKs⟩ := (krullTopology_mem_nhds_one_iff L Ω s).mp hs
  haveI : FiniteDimensional E K := Module.Finite.trans L K
  haveI : FiniteDimensional E (K.restrictScalars E) := inferInstanceAs (FiniteDimensional E K)
  have hopen := (K.restrictScalars E).fixingSubgroup_isOpen
  refine Filter.mem_of_superset ((hopen.preimage continuous_subtype_val).mem_nhds ?_) ?_
  · exact (K.restrictScalars E).fixingSubgroup.one_mem
  · intro t ht
    apply hKs
    rw [Set.mem_preimage, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at ht
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hι]
    exact ht x ((IntermediateField.mem_restrictScalars E).mpr hx)
