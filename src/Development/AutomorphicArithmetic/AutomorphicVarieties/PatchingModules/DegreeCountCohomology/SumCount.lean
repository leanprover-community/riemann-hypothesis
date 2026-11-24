module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.sumCount :
    ∀ (R D M : Type) [CommRing R] [Group D] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R D M) (b : AddSubgroup M) (Z : AddSubgroup (D → M)), Finite Z → (∀ y ∈ b, (fun g => ρ g y - y) ∈ Z) → Finite ((Bl ρ).toAddSubgroup ⊔ Z : AddSubgroup (D → M)) ∧ Nat.card ((Bl ρ).toAddSubgroup ⊔ Z : AddSubgroup (D → M)) * Nat.card b ≤ Nat.card M * Nat.card Z := by
  intro R D M _ _ _ _ _ ρ b Z hZ hb
  let d : M →ₗ[R] (D → M) := LinearMap.pi fun g => ρ g - LinearMap.id
  have hd : ∀ y, d y = fun g => ρ g y - y := fun y => rfl
  let φ : M × Z →+ (D → M) := d.toAddMonoidHom.coprod Z.subtype
  have hφ : ∀ p : M × Z, φ p = d p.1 + p.2 := fun p => rfl
  have hr : φ.range = (Bl ρ).toAddSubgroup ⊔ Z := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [hφ]
      exact AddSubgroup.add_mem_sup (show d p.1 ∈ (Bl ρ).toAddSubgroup from ⟨p.1, rfl⟩) p.2.2
    · refine sup_le ?_ ?_
      · rintro _ ⟨y, rfl⟩
        exact ⟨(y, 0), by rw [hφ]; exact add_zero _⟩
      · intro z hz
        exact ⟨(0, ⟨z, hz⟩), by rw [hφ]; simp⟩
  rw [← hr]
  have hfin : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  refine ⟨hfin, ?_⟩
  have h1 : Nat.card (M × Z) = Nat.card φ.range * Nat.card φ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv]
  have h2 : Nat.card b ≤ Nat.card φ.ker := by
    let ι : b → φ.ker := fun y => ⟨(y.1, -⟨fun g => ρ g y.1 - y.1, hb y.1 y.2⟩), by
      rw [AddMonoidHom.mem_ker, hφ, hd]
      exact add_neg_cancel _⟩
    refine Nat.card_le_card_of_injective ι fun y y' h => ?_
    exact Subtype.ext (congrArg (fun p : φ.ker => p.1.1) h)
  rw [← Nat.card_prod M Z, h1]
  exact Nat.mul_le_mul_left _ h2
