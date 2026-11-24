module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField
public import GroundTheory.GlobalFields.TateThesis.Chebotarev
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
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.ExistsPrimeAbsNormOfHasDirichletDensity

@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

namespace PositivityTheory.KB.PrincipalPrimes

theorem exists_principal (L : Type) [Field L] [NumberField L] (T : Set (HeightOneSpectrum (𝓞 L)))
    (hT : T.Finite) : ∃ v : HeightOneSpectrum (𝓞 L), v ∉ T ∧ v.asIdeal.IsPrincipal := by
  let Ω := AlgebraicClosure L
  let H := GroundTheory.Global.hilbertClassField L Ω
  have : NumberField H := NumberField.of_module_finite L H
  have : IsGalois L H := inferInstance
  have hd := GroundTheory.Global.hasDirichletDensity_setOf_exists_arithFrobAt_mem (K := L) (L := H)
    ({1} : Set (H ≃ₐ[L] H)) (by
      intro σ hσ τ
      rw [Set.mem_singleton_iff] at hσ ⊢
      rw [hσ, mul_one, mul_inv_cancel])
  have hpos : (0 : ℝ) < (Nat.card ({1} : Set (H ≃ₐ[L] H)) : ℝ) / Nat.card (H ≃ₐ[L] H) :=
    div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  obtain ⟨v, ⟨-, w, hw, hF⟩, hvT, -⟩ :=
    ReciprocityTheory.Neutral.Bridge.exists_prime_absNorm_of_hasDirichletDensity hd hpos hT
  refine ⟨v, hvT, ?_⟩
  have := hw
  have h1 := GroundTheory.Global.hilbertClassFieldArtinEquiv_mk0 L Ω v w
  rw [Set.mem_singleton_iff.1 hF, MulEquiv.map_eq_one_iff] at h1
  exact (ClassGroup.mk0_eq_one_iff _).1 h1

theorem finite_small (L : Type) [Field L] [NumberField L] (B : ℕ) :
    {v : HeightOneSpectrum (𝓞 L) | Ideal.absNorm v.asIdeal ≤ B}.Finite :=
  Set.Finite.preimage (f := fun v : HeightOneSpectrum (𝓞 L) => v.asIdeal)
    (fun _ _ _ _ h => HeightOneSpectrum.ext h) (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 L) B)

theorem exists_prime (L : Type) [Field L] [NumberField L] (B : ℕ) :
    ∃ π : 𝓞 L, Prime π ∧ B ≤ Ideal.absNorm (Ideal.span {π}) := by
  obtain ⟨v, hv, π, hπ⟩ := exists_principal L _ (finite_small L B)
  have hπ' : v.asIdeal = Ideal.span {π} := hπ
  have hne : π ≠ 0 := by
    rintro rfl
    exact v.ne_bot (by rw [hπ', Ideal.span_singleton_eq_bot])
  refine ⟨π, (Ideal.span_singleton_prime hne).1 (hπ' ▸ v.isPrime), ?_⟩
  rw [← hπ']
  simp only [Set.mem_ofPred_eq, not_le] at hv
  omega

end PositivityTheory.KB.PrincipalPrimes
