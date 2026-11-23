module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import ReciprocityTheory.NeutralLocalFields.HilbertClassField
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdeleClassGroupHomOpenKernelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaElementEqOneOrLiesAboveFinitePlaceStatement
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

@[expose] public section

open NumberField IsDedekindDomain Neutral.HilbertClassField

open Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.IdealArtinSymbol

theorem exists_artinSymbol : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E),
      IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧
      (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v →
        IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  intro H E Ω _ _ _ _ _
  obtain ⟨art, ha⟩ := H E Ω
  obtain ⟨cl, hclo, hclk, hunit, hunif⟩ := GlobalTheory.T.exists_ideleClassGroupHom_open_kernel E
  have hker : art.ker ≤ cl.ker := by
    rw [ha.ker]
    exact Subgroup.topologicalClosure_minimal _ hclk (Subgroup.isClosed_of_isOpen _ hclo)
  let ρ := art.liftOfSurjective ha.quot.surjective ⟨cl, hker⟩
  have hρ : ∀ x, ρ (art x) = cl x := fun x => art.liftOfRightInverse_comp_apply _ _ ⟨cl, hker⟩ x
  have hρo : IsOpen (ρ.ker : Set (Gab E Ω)) := by
    rw [← ha.quot.isQuotientMap.isOpen_preimage]
    convert hclo using 1
    ext x
    rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe, MonoidHom.mem_ker, hρ, MonoidHom.mem_ker]
  let ψ : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E) := ρ.comp (toAb E Ω)
  have hlies : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), LiesAbove A v → IsPlaceOver A v :=
    fun v A h x => by rw [← h x, A.mem_nonunits_iff]
  refine ⟨ψ⁻¹, ?_, ?_, ?_⟩
  · have e : ((ψ⁻¹).ker : Set (Ω ≃ₐ[E] Ω)) = toAb E Ω ⁻¹' (ρ.ker : Set (Gab E Ω)) := by
      ext σ
      simp [ψ, MonoidHom.mem_ker]
    rw [e]
    exact hρo.preimage QuotientGroup.continuous_mk
  · intro A g hg
    rcases GlobalTheory.T.inertiaElement_eq_one_or_liesAbove_finitePlace E Ω A g hg with rfl | ⟨v, hv⟩
    · exact map_one _
    have hI : g ∈ Ine (F := E) A := ⟨hg.1, fun x hx => by
      rw [← A.mem_nonunits_iff]
      exact hg.2 x ((A.valuation_le_one_iff x).1 hx)⟩
    obtain ⟨x, _, hx⟩ := (ha.ine v A (hlies v A hv) (toAb E Ω g)).2 ⟨g, hI, rfl⟩
    have : ψ g = 1 := by
      show ρ (toAb E Ω g) = 1
      rw [← hx, hρ]
      exact hunit v x ‹_›
    rw [MonoidHom.inv_apply, this, inv_one]
  · intro v A φ hv hφ
    have hF : IsFrob (F := E) A (normV v) φ := ⟨hφ.1, fun x hx => by
      rw [← A.mem_nonunits_iff]
      exact hφ.2 x ((A.valuation_le_one_iff x).1 hx)⟩
    obtain ⟨x, hxu, hx⟩ := (ha.frob v A (hlies v A hv) (toAb E Ω φ⁻¹)).2 ⟨φ, hF, rfl⟩
    rw [MonoidHom.inv_apply, ← map_inv]
    show ρ (toAb E Ω φ⁻¹) = _
    rw [← hx, hρ]
    exact hunif v x hxu

end GlobalTheory.IdealArtinSymbol
