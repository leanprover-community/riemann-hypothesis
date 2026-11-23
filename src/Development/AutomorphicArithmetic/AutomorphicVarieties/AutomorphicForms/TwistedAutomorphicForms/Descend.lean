module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

theorem UpperTheory.V.Af.Tw.descend :
    UpperTheory.V.Af.Tw.Descend := by
  unfold UpperTheory.V.Af.Tw.Descend
  intro F Ω B _ _ _ _ _ _ _ _ art hart ψ hψc hdiag hfin
  have hq := hart.quot
  have hker : art.ker ≤ ψ.ker := by
    rw [hart.ker]
    refine Subgroup.topologicalClosure_minimal _ ?_ ?_
    · refine sup_le ?_ ?_
      · rintro _ ⟨k, rfl⟩
        exact hdiag k
      · intro z hz
        unfold infConn at hz
        obtain ⟨w, _, rfl⟩ := hz
        exact hfin _ rfl
    · exact isClosed_singleton.preimage hψc
  let fC : C(Ideles F, Gab F Ω) := ⟨art, hq.continuous⟩
  let gC : C(Ideles F, B) := ⟨ψ, hψc⟩
  have hfact : Function.FactorsThrough gC fC := by
    intro a b hab
    have hab' : a / b ∈ art.ker := by
      rw [MonoidHom.mem_ker, map_div]
      exact div_eq_one.2 hab
    have := hker hab'
    rw [MonoidHom.mem_ker, map_div] at this
    exact div_eq_one.1 this
  have hQ : Topology.IsQuotientMap fC := hq.isQuotientMap
  let κC := hQ.lift gC hfact
  have hκ : ∀ x, κC (art x) = ψ x := fun x => DFunLike.congr_fun (hQ.lift_comp gC hfact) x
  let κ₀ : Gab F Ω →* B := MonoidHom.mk' κC (by
    intro a b
    obtain ⟨x, rfl⟩ := hq.surjective a
    obtain ⟨y, rfl⟩ := hq.surjective b
    rw [← map_mul, hκ, hκ, hκ, map_mul])
  refine ⟨κ₀.comp (GlobalTheory.HeckeGal.toAb F Ω), ?_, ?_⟩
  · exact κC.continuous.comp (by
      first
        | exact QuotientGroup.continuous_mk
        | exact continuous_quot_mk)
  · intro x σ h
    show κC (GlobalTheory.HeckeGal.toAb F Ω σ) = ψ x
    rw [← h, hκ]
