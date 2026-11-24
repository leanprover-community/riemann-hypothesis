module

public import GroundTheory.AutomorphicForms.QuotientMeasure
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.RightCosetSpace

theorem UpperTheory.ConvolutionTheory.K.qmapPres :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
      (μ : Measure G) [μ.IsHaarMeasure] (e : G ≃ₜ* G), (∀ g, e g ∈ Γ ↔ g ∈ Γ) → MeasurePreserving e μ μ →
      (∀ x : G, mk Γ (e (Quotient.out (mk Γ x))) = mk Γ (e x)) ∧
      MeasurePreserving (fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) (quotientMeasure Γ μ) (quotientMeasure Γ μ) := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ e hΓ he
  have h1 : ∀ x : G, mk Γ (e (Quotient.out (mk Γ x))) = mk Γ (e x) := by
    intro x
    have h0 : mk Γ (Quotient.out (mk Γ x)) = mk Γ x := Quotient.out_eq _
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 h0
    rw [← hγ]
    change mk Γ (e ((γ : G) * x)) = _
    rw [map_mul]
    exact mk_mul_of_mem ((hΓ _).2 γ.2) _
  have hcomm : (fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) ∘ mk Γ = mk Γ ∘ e :=
    funext h1
  have hm : Measurable (fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) := by
    rw [measurable_from_quotient]
    change Measurable ((fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) ∘ mk Γ)
    rw [hcomm]
    exact (measurable_mk Γ).comp he.measurable
  refine ⟨h1, hm, ?_⟩
  let ε : Γ → Γ := fun γ => ⟨e.symm γ, (hΓ _).1 (by simpa using γ.2)⟩
  have hε : Function.Bijective ε := by
    constructor
    · intro a b hab
      exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
    · intro b
      exact ⟨⟨e b, (hΓ _).2 b.2⟩, Subtype.ext (by simp [ε])⟩
  have hF' : IsFundamentalDomain Γ (e ⁻¹' fundamentalDomain Γ) μ :=
    (isFundamentalDomain_fundamentalDomain Γ μ).preimage_of_equiv
      he.quasiMeasurePreserving (e := ε) hε fun γ x => by
        change e (e.symm γ * x) = (γ : G) * e x
        simp
  have key := map_restrict_eq_quotientMeasure μ hF'
  conv_lhs => rw [← key]
  rw [Measure.map_map hm (measurable_mk Γ), hcomm, ← Measure.map_map (measurable_mk Γ) he.measurable,
    ← Measure.restrict_map he.measurable (measurableSet_fundamentalDomain Γ), he.map_eq]
  rfl
