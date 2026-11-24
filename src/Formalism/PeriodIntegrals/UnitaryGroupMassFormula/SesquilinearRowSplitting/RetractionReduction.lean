module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoordStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorsionFreeGenerators.ProjectiveReduction
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

namespace PI.SRW

theorem retraction_reduction : RetrStep := by
  intro E V _ _ _ _ _ _ Λ N hNΛ hfg hsat
  let N' : Submodule (𝓞 E) Λ := N.comap Λ.subtype
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite (𝓞 E) (Λ ⧸ N') := inferInstance
  haveI : NoZeroSMulDivisors (𝓞 E) (Λ ⧸ N') := by
    refine ⟨fun {o q} hq => ?_⟩
    by_cases ho : o = 0
    · exact Or.inl ho
    right
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N' q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hsat o x ho x.2 hq
  haveI : Module.Projective (𝓞 E) (Λ ⧸ N') := PI.FGTFG.projective_reduction (𝓞 E) (Λ ⧸ N')
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N'.mkQ LinearMap.id (Submodule.mkQ_surjective N')
  let ρ' : Λ →ₗ[𝓞 E] Λ := LinearMap.id - s.comp N'.mkQ
  have hρ' : ∀ x : Λ, ρ' x ∈ N' := by
    intro x
    have h1 : N'.mkQ (ρ' x) = 0 := by
      have h2 := LinearMap.congr_fun hs (N'.mkQ x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
      show N'.mkQ (x - s (N'.mkQ x)) = 0
      rw [map_sub, h2, sub_self]
    simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h1
  refine ⟨Λ.subtype.comp ρ', fun x => hρ' x, fun x hx => ?_⟩
  have hx' : x ∈ N' := hx
  have h0 : N'.mkQ x = 0 := by simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx'
  simp [ρ', h0]

end PI.SRW
