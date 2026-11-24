module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace RenameMultiProjPrime

variable {S K' : Type} [DecidableEq S] [DecidableEq K'] {κ : S → Type} {ι' : K' → Type} (E : S ≃ K')
  (σ : (Σ s, κ s) ≃ (Σ k', ι' k'))

theorem weight_mapDomain (hσ : ∀ v, (σ v).1 = E v.1) (d : (Σ s, κ s) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain σ d) =
      Finsupp.weight (blockWeight κ) d ∘ E.symm := by
  induction d using Finsupp.induction_linear with
  | zero => funext k; simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), hf, hg]
    rfl
  | single v n =>
    rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
    funext k
    simp only [blockWeight, hσ, Function.comp_apply, Pi.smul_apply, Pi.single_apply,
      Equiv.symm_apply_eq, smul_eq_mul]

theorem rename_weightedHomogeneousComponent {R : Type u} [CommRing R]
    (hσ : ∀ v, (σ v).1 = E v.1) (b : S → ℕ) (f : MRing κ R) :
    rename σ (weightedHomogeneousComponent (blockWeight κ) b f) =
      weightedHomogeneousComponent (blockWeight ι') (b ∘ E.symm) (rename σ f) := by
  classical
  ext m
  have hm : m = Finsupp.mapDomain σ (Finsupp.mapDomain σ.symm m) := by
    rw [← Finsupp.mapDomain_comp, Equiv.self_comp_symm, Finsupp.mapDomain_id]
  rw [hm, coeff_weightedHomogeneousComponent, coeff_rename_mapDomain _ σ.injective,
    coeff_rename_mapDomain _ σ.injective, coeff_weightedHomogeneousComponent,
    weight_mapDomain E σ hσ]
  have hiff : Finsupp.weight (blockWeight κ) (Finsupp.mapDomain σ.symm m) ∘ E.symm = b ∘ E.symm ↔
      Finsupp.weight (blockWeight κ) (Finsupp.mapDomain σ.symm m) = b :=
    E.symm.surjective.injective_comp_right.eq_iff
  simp only [hiff]

end RenameMultiProjPrime

theorem RenameMultiProjPrime.proof : RenameMultiProjPrime.Statement.{u} := by
  intro R _ S K' _ _ κ ι' E σ hσ P hP
  refine ⟨?_, ?_, ?_⟩
  · have := hP.isPrime
    exact Ideal.comap_isPrime _ _
  · intro f hf b
    rw [Ideal.mem_comap] at hf ⊢
    rw [RenameMultiProjPrime.rename_weightedHomogeneousComponent (R := R) E σ hσ b f]
    exact hP.multiHomog _ hf _
  · intro s
    obtain ⟨i', hi'⟩ := hP.relevant (E s)
    obtain ⟨⟨s', i⟩, hv⟩ : ∃ v, σ v = ⟨E s, i'⟩ := σ.surjective _
    have hs : s' = s := E.injective (by simpa [hv] using (hσ ⟨s', i⟩).symm)
    subst hs
    refine ⟨i, ?_⟩
    rw [Ideal.mem_comap, rename_X, hv]
    exact hi'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
