module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousBijectiveAbelianizationOfAlgEqui
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

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeGal

def conjGal {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) :
    (Ω' ≃ₐ[E'] Ω') →* (Ω ≃ₐ[E] Ω) where
  toFun τ :=
    { toRingEquiv := (φ.trans τ.toRingEquiv).trans φ.symm
      commutes' := fun x => by
        show φ.symm (τ (φ (algebraMap E Ω x))) = algebraMap E Ω x
        rw [hφ, AlgEquiv.commutes, ← hφ, RingEquiv.symm_apply_apply] }
  map_one' := by
    ext z
    show φ.symm (φ z) = z
    exact φ.symm_apply_apply z
  map_mul' τ τ' := by
    ext z
    show φ.symm ((τ * τ') (φ z)) = φ.symm (τ (φ (φ.symm (τ' (φ z)))))
    rw [RingEquiv.apply_symm_apply]
    rfl

theorem conjGal_apply {E Ω E' Ω' : Type} [Field E] [Field Ω] [Algebra E Ω] [Field E'] [Field Ω'] [Algebra E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x))
    (τ : Ω' ≃ₐ[E'] Ω') (z : Ω) : conjGal φ j hφ τ z = φ.symm (τ (φ z)) := rfl

theorem exists_abHom_of_ringEquiv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    (φ : Ω ≃+* Ω') (j : E →+* E'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (j x)) →
    ∃ ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω, Continuous ρ ∧
      ∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) →
        ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  intro E Ω _ _ _ _ _ E' Ω' _ _ _ _ _ φ j hφ
  haveI : Algebra.IsIntegral E' Ω' := (IsAlgClosure.isAlgebraic (R := E') (K := Ω')).isIntegral
  haveI : IsClosed ((commutator (Formalism.ConjugateSelfDual.G E Ω)).topologicalClosure : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  let c := conjGal φ j hφ
  have hc : Continuous c :=
    continuous_galHom_of_fix c fun y => ⟨φ y, fun τ hτ => by
      rw [conjGal_apply, hτ, RingEquiv.symm_apply_apply]⟩
  let r : Formalism.ConjugateSelfDual.G E' Ω' →* Gab E Ω := (toAb E Ω).comp c
  have hr : Continuous r := QuotientGroup.continuous_mk.comp hc
  refine ⟨liftAb r hr, continuous_liftAb r hr, fun τ σ h => ?_⟩
  rw [liftAb_toAb]
  show toAb E Ω (c τ) = toAb E Ω σ
  congr 1
  ext z
  rw [conjGal_apply, ← h, RingEquiv.symm_apply_apply]

end GlobalTheory.HeckeGal
