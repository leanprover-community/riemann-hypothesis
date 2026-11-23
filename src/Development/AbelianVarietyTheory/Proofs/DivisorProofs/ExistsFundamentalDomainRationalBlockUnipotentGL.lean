module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

noncomputable section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open Topology

namespace GlobalTheory.CuspRep

theorem discreteTopology_ratN (E : Type) [Field E] [NumberField E] (a s : ℕ) :
    DiscreteTopology (ratN E a s) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hU : IsOpen (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd (F := E)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => Formalism.IndefR.Eqv.G5.adl_isOpen_nbhd
  have h : ({0} : Set (ratN E a s)) =
      Subtype.val ⁻¹' (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd (F := E)) := by
    ext ⟨x, q, hq⟩
    constructor
    · intro hx p _
      have : x = 0 := congrArg Subtype.val hx
      subst this
      exact Formalism.IndefR.Eqv.G5.adl_zero_mem_nbhd
    · intro hx
      subst hq
      apply Subtype.ext
      funext p
      have h0 : q p = 0 := Formalism.IndefR.Eqv.G5.adl_eq_zero_of_mem_nbhd (q p) (hx p (Set.mem_univ _))
      show algebraMap E (Ad E) (q p) = 0
      rw [h0, map_zero]
  rw [h]
  exact hU.preimage continuous_subtype_val

theorem exists_isAddFundamentalDomain_ratN : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ) [MeasurableSpace (BlockIx a s → Ad E)] [BorelSpace (BlockIx a s → Ad E)] (μ : Measure (BlockIx a s → Ad E)) [μ.IsAddHaarMeasure], ∃ 𝓕 : Set (BlockIx a s → Ad E), IsAddFundamentalDomain (ratN E a s) 𝓕 μ ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 < ⊤ := by
  intro E _ _ _ a s _ _ μ _
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := discreteTopology_ratN E a s
  haveI := countable_ratN (E := E) (a := a) s
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (ratN E a s)
  haveI : MeasurableConstVAdd (ratN E a s) (BlockIx a s → Ad E) :=
    ⟨fun γ => (continuous_const.add continuous_id :
      Continuous fun x : BlockIx a s → Ad E => (γ : BlockIx a s → Ad E) + x).measurable⟩
  haveI : VAddInvariantMeasure (ratN E a s) (BlockIx a s → Ad E) μ :=
    ⟨fun γ t _ => measure_preimage_add μ (γ : BlockIx a s → Ad E) t⟩
  have hμ : μ ≠ 0 := fun h => by
    have := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    rw [h] at this
    exact this rfl
  exact ⟨D, hD μ, (hD μ).measure_ne_zero hμ, covol_lt_top μ D (hD μ)⟩

end GlobalTheory.CuspRep
