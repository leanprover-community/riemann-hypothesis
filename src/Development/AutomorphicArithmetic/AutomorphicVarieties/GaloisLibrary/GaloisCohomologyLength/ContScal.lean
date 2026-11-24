module

public import Formalism.GaloisCohomology.Statement
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
import Mathlib.NumberTheory.Padics.LocalField
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.contScal :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ψ : Γ →* ℤ_[l]ˣ), (Continuous fun g => ((ψ g : ℤ_[l]ˣ) : ℤ_[l])) → ContAction (scalRep (QZ l) ψ) := by
  intro l _ Γ _ _ ψ hψ
  haveI hd : DiscreteTopology (QZ l) := ⟨rfl⟩
  unfold ReciprocityTheory.Gal.ContAction
  apply continuous_prod_of_discrete_right.mpr
  intro a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
  let q : ℚ_[l] → QZ l := fun z => Submodule.Quotient.mk z
  have hmk : Continuous q := by
    refine (continuous_discrete_rng (β := QZ l)).mpr ?_
    intro b
    obtain ⟨y, rfl⟩ : ∃ y, q y = b := Submodule.Quotient.mk_surjective (ZlSub l) b
    have e : q ⁻¹' {q y} = Metric.closedBall y 1 := by
      ext z
      have h1 : q z = q y ↔ z - y ∈ ZlSub l := Submodule.Quotient.eq (ZlSub l)
      rw [Set.mem_preimage, Set.mem_singleton_iff, h1, LinearMap.mem_range,
        Metric.mem_closedBall, dist_eq_norm]
      constructor
      · rintro ⟨w, hw⟩
        rw [← hw]
        exact w.norm_le_one
      · intro h
        exact ⟨⟨z - y, h⟩, rfl⟩
    rw [e]
    exact IsUltrametricDist.isOpen_closedBall y one_ne_zero
  have hc : Continuous fun g : Γ => ((ψ g : ℤ_[l]) : ℚ_[l]) * x :=
    (continuous_subtype_val.comp hψ).mul continuous_const
  refine (hmk.comp hc).congr ?_
  intro g
  rfl
