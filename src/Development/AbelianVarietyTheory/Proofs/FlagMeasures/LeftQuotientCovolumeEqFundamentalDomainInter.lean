module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqMeasureInterFundamentalDom
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalPointsCountableDiscreteSubgroupAdelic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.CovolRat

theorem covol_eq_inter_fund : ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund A : Set I.GA), I.IsFundDom (I.muA μf) fund → MeasurableSet A → (∀ γ ∈ I.GFset, ∀ x ∈ A, γ * x ∈ A) → covol I.GFset (I.muA μf) A = I.muA μf (A ∩ fund) ∧ 0 < I.muA μf fund := by
  intro I μf _ _ fund A hfund hA hinv
  obtain ⟨hleft, -, -, -, hopen⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular I μf
  obtain ⟨⟨Γ, hΓ⟩, hcount, -⟩ := GlobalTheory.RatDiscrete.subgroup_countable_discrete I
  obtain ⟨hmeas, hcov, hdisj⟩ := hfund

  have hm : ∀ γ, γ ∈ Γ ↔ γ ∈ I.GFset := fun γ => by rw [← hΓ]; exact SetLike.mem_coe.symm
  refine ⟨?_, ?_⟩
  · have key := GlobalTheory.covol_eq_measure_inter_fund I.GA Γ (I.muA μf) fund A (by rw [hΓ]; exact hcount)
      (fun γ _ => hleft γ) hmeas
      (fun y => by obtain ⟨γ, hγ, h⟩ := hcov y; exact ⟨γ, (hm γ).2 hγ, h⟩)
      (fun γ hγ h1 => hdisj γ ((hm γ).1 hγ) h1) hA (fun γ hγ x hx => hinv γ ((hm γ).1 hγ) x hx)
    rw [hΓ] at key
    exact key
  ·
    rw [pos_iff_ne_zero]
    intro h0
    have hpre : ∀ γ : I.GA, I.muA μf ((fun y => γ * y) ⁻¹' fund) = 0 := by
      intro γ
      rw [← Measure.map_apply (measurable_const_mul γ) hmeas, hleft γ, h0]
    have hsub : (Set.univ : Set I.GA) ⊆ ⋃ γ ∈ I.GFset, (fun y => γ * y) ⁻¹' fund := by
      intro y _
      obtain ⟨γ, hγ, h⟩ := hcov y
      exact Set.mem_biUnion hγ h
    have hnull : I.muA μf Set.univ = 0 :=
      measure_mono_null hsub ((measure_biUnion_null_iff hcount).2 fun γ _ => hpre γ)
    have hpos := hopen Set.univ isOpen_univ ⟨1, trivial⟩
    rw [hnull] at hpos
    exact lt_irrefl _ hpos

end GlobalTheory.CovolRat
