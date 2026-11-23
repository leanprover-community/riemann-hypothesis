module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.FlagHeight

theorem exists_rat_translate_height_le : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C := by
  intro D S S₀ ρ d
  obtain ⟨KU, hKU, hU⟩ := GlobalTheory.UnitU.cocompact D ρ
  obtain ⟨KR, hKR, hR⟩ := GlobalTheory.Unf.FlagSub.radX_cocompact d
  have hlv : Continuous (GlobalTheory.JacMeas.lv d) := d.continuous_levi.comp continuous_subtype_val
  have hc : Continuous fun q : radX d × UX D ρ => q.1.1 * GlobalTheory.JacMeas.lv d q.2 :=
    (continuous_subtype_val.comp continuous_fst).mul (hlv.comp continuous_snd)
  have hK : IsCompact ((fun q : radX d × UX D ρ => q.1.1 * GlobalTheory.JacMeas.lv d q.2) '' (KR ×ˢ KU)) :=
    (hKR.prod hKU).image hc
  obtain ⟨C, hC⟩ := exists_height_le_of_isCompact S hK
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨n₀, hn₀, u, rfl⟩ := GlobalTheory.JacMeas.exists_rad_lv d hn
  obtain ⟨γu, hγu, k, hk, rfl⟩ := hU u
  have hr : (GlobalTheory.JacMeas.lv d γu)⁻¹ * n₀ * ((GlobalTheory.JacMeas.lv d γu)⁻¹)⁻¹ ∈ radX d := by
    have := GlobalTheory.JacMeas.lv_conj d n₀ hn₀ γu⁻¹
    simpa [map_inv] using this
  obtain ⟨γr, hγr, kr, hkr, hrk⟩ := hR ⟨_, hr⟩
  have hlvQ : GlobalTheory.JacMeas.lv d γu ∈ GQ S := d.levi_mem_GQ hγu.1 hγu.2
  have hγrQ : (γr : GA D S) ∈ GQ S := Subgroup.mem_subgroupOf.1 hγr
  refine ⟨(γr : GA D S)⁻¹ * (GlobalTheory.JacMeas.lv d γu)⁻¹, mul_mem (inv_mem hγrQ) (inv_mem hlvQ),
    mul_mem (inv_mem (GlobalTheory.JacMeas.radX_le d γr.2)) (inv_mem (GlobalTheory.JacMeas.lv_mem d γu)), ?_⟩
  apply hC
  refine ⟨(kr, k), ⟨hkr, hk⟩, ?_⟩
  have e : ((γr : GA D S) * kr) = (GlobalTheory.JacMeas.lv d γu)⁻¹ * n₀ * ((GlobalTheory.JacMeas.lv d γu)⁻¹)⁻¹ := by
    have := congrArg Subtype.val hrk
    simpa using this.symm
  simp only
  rw [map_mul]
  calc (kr : GA D S) * GlobalTheory.JacMeas.lv d k
      = (γr : GA D S)⁻¹ * ((γr : GA D S) * kr) * GlobalTheory.JacMeas.lv d k := by group
    _ = _ := by rw [e]; group

end GlobalTheory.FlagHeight
