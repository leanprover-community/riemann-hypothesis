module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WBMemLatS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem prod_eq_t_mul_unit_count : ∀ {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (t : ι → Formalism.Per6.BdRp l) (i₀ : ι), i₀ ∈ s →
    ∀ u : (Formalism.Per6.BdRp l)ˣ, ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l * (u : Formalism.Per6.BdRp l) →
      thB l (t i₀) = 0 →
      ∀ μ ∈ s, (μ = i₀ → t μ ∉ FB l 2) ∧ (μ ≠ i₀ → t μ ∉ FB l 1) := by
  intro l _ ι s t i₀ hi₀ u hprod h0 μ hμ
  have hmax : IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) = Ideal.span {GroundTheory.PAdicHodge.tBdR l} :=
    GroundTheory.PAdicHodge.maximalIdeal_eq_span_fontaineT GroundTheory.PAdicHodge.untilt_epsilon
      GroundTheory.PAdicHodge.untilt_frobeniusEquiv_symm_epsilon_ne_one
  have htirr : Irreducible (GroundTheory.PAdicHodge.tBdR l) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2 hmax
  have hFB : ∀ k, FB l k = Ideal.span {GroundTheory.PAdicHodge.tBdR l ^ k} := fun k => by
    rw [FB, ker_thB_eq, hmax, Ideal.span_singleton_pow]
  have hnot : ¬ (GroundTheory.PAdicHodge.tBdR l ^ 2 ∣ ∏ μ ∈ s, t μ) := by
    rw [hprod, pow_two]
    intro h
    have h1 : GroundTheory.PAdicHodge.tBdR l ∣ (u : Formalism.Per6.BdRp l) :=
      (mul_dvd_mul_iff_left htirr.ne_zero).1 h
    exact htirr.not_isUnit (isUnit_of_dvd_unit h1 u.isUnit)
  have hi : GroundTheory.PAdicHodge.tBdR l ∣ t i₀ := by
    have : t i₀ ∈ FB l 1 := by
      rw [FB, pow_one, RingHom.mem_ker]; exact h0
    rw [hFB, pow_one] at this
    exact Ideal.mem_span_singleton.1 this
  refine ⟨fun e hm => hnot ?_, fun hne hm => hnot ?_⟩
  · subst e
    rw [hFB] at hm
    exact (Ideal.mem_span_singleton.1 hm).trans (Finset.dvd_prod_of_mem t hμ)
  · rw [hFB, pow_one] at hm
    have hd := Ideal.mem_span_singleton.1 hm
    have hμ' : μ ∈ s.erase i₀ := Finset.mem_erase.2 ⟨hne, hμ⟩
    rw [← Finset.mul_prod_erase s t hi₀, ← Finset.mul_prod_erase (s.erase i₀) t hμ', pow_two, ← mul_assoc]
    exact (mul_dvd_mul hi hd).mul_right _

end GlobalTheory.CompanionTheory.LTPer
