module

public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.UnitsBasic
public import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
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
import Mathlib.RepresentationTheory.Rep.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem exists_uniformizer_ord' (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : 𝓞 F, ϖ ∈ v.asIdeal ∧ ϖ ∉ v.asIdeal ^ 2 ∧
      ord ((ϖ : F) : v.adicCompletion F) = 1 := by
  have hlt : v.asIdeal ^ (1 + 1) < v.asIdeal ^ 1 := Ideal.pow_succ_lt_pow v.ne_bot 1
  rw [pow_one] at hlt
  obtain ⟨ϖ, hϖ, hϖ2⟩ := SetLike.exists_of_lt hlt
  refine ⟨ϖ, hϖ, hϖ2, ?_⟩
  apply GroundTheory.Global.ord_eq_one_of_valued_eq_exp
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Ideal.zero_mem _)
  have hne := v.intValuation_ne_zero ϖ h0
  have h1 : v.intValuation ϖ ≤ WithZero.exp (-(1 : ℕ) : ℤ) :=
    (v.intValuation_le_pow_iff_mem ϖ 1).2 (by rwa [pow_one])
  have h2 : ¬ v.intValuation ϖ ≤ WithZero.exp (-(2 : ℕ) : ℤ) := fun h =>
    hϖ2 ((v.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have hval : v.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
    rw [← WithZero.exp_log hne] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    push_cast at h1 h2
    omega
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (HeightOneSpectrum.valuation_of_algebraMap v ϖ).trans hval

end PositivityTheory.Lit1.PTN
