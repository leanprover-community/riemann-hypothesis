module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GLOneChar

open GlobalTheory.SmGL

theorem equiv_detRep_of_isIrreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ), d = 1 → σ.IsIrreducible → GlobalTheory.SmGL.HasCentralChar σ ω → Nonempty (σ.Equiv (GlobalTheory.SmGL.detRep (Fin d) ω)) := by
  intro k _ _ _ _ d V _ _ σ ω hd hirr hω
  have hact : ∀ (g : GL (Fin d) k) (v : V), σ g v = (ω (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    intro g v
    conv_lhs => rw [GlobalTheory.ProdSupport.eq_scalar_det hd g]
    exact hω _ v
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : (⊥ : Subrepresentation σ) = ⊤ :=
      Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation σ := ⟨ℂ ∙ v, fun g w hw => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [hact, smul_smul]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩⟩
  have hS : S = ⊤ := by
    rcases eq_bot_or_eq_top S with h | h
    · exfalso
      have : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
      rw [h] at this
      exact hv this
    · exact h
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℂ V v) := by
    intro w
    have hw : w ∈ S.toSubmodule := by rw [hS]; trivial
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    exact ⟨c, rfl⟩
  have hinj : Function.Injective (LinearMap.toSpanSingleton ℂ V v) := by
    intro a b hab
    simp only [LinearMap.toSpanSingleton_apply] at hab
    exact smul_left_injective ℂ hv hab
  let e : ℂ ≃ₗ[ℂ] V := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨(Representation.Equiv.mk e fun g => ?_).symm⟩
  ext c
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, e,
    LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, detRep, ofChar_apply,
    detChar_apply, hact, smul_smul, smul_eq_mul]
  rw [mul_one, ← LinearEquiv.map_smul, smul_eq_mul, mul_one]

end GlobalTheory.GLOneChar
