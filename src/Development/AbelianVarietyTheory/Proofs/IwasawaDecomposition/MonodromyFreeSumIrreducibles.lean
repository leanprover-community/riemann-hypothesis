module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
  GlobalTheory.LocLanglands Module

namespace GlobalTheory.WeilDeligne.IrrDecomp

theorem isIrreducible_of_equiv {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : V ≃ₗ[ℂ] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (hρ : ρ.IsIrreducible) :
    ρ'.IsIrreducible := by
  have he' : ∀ g v, e.symm (ρ' g v) = ρ g (e.symm v) := fun g v => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  let F : Subrepresentation ρ ≃o Subrepresentation ρ' :=
    { toFun := fun U => ⟨U.toSubmodule.map (e : V →ₗ[ℂ] V'), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ g u, U.apply_mem_toSubmodule g hu, he g u⟩⟩
      invFun := fun U => ⟨U.toSubmodule.map (e.symm : V' →ₗ[ℂ] V), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ' g u, U.apply_mem_toSubmodule g hu, he' g u⟩⟩
      left_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      right_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      map_rel_iff' := by
        intro U U'
        show U.toSubmodule.map (e : V →ₗ[ℂ] V') ≤ U'.toSubmodule.map (e : V →ₗ[ℂ] V') ↔
          U.toSubmodule ≤ U'.toSubmodule
        exact Submodule.map_le_map_iff_of_injective e.injective _ _ }
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  exact F.symm.isSimpleOrder

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.WeilDeligne.IrrDecomp
