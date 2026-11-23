module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Topology.Instances.AddCircle.Defs
public import GroundTheory.ProfiniteCohomology.CyclicCup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory groupCohomology GroundTheory.GroupCoh

section Cyclicity

variable {G : Type} [Group G]

theorem isCyclic_of_injective_char [Finite G] (χ : Additive G →+ AddCircle (1 : ℚ))
    (hχ : Function.Injective χ) : IsCyclic G := by
  classical
  have := Fintype.ofFinite G
  set m := Fintype.card G with hmdef
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have : Subsingleton G := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    infer_instance
  have hk : ∀ x : G, ∃ k : ℕ, k < m ∧
      ((((k : ℚ) / m : ℚ)) : AddCircle (1 : ℚ)) = χ (Additive.ofMul x) := by
    intro x
    have hy01 := reprIco_mem (χ (Additive.ofMul x))
    have h0 : (((m : ℚ) * reprIco (χ (Additive.ofMul x)) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
      rw [← nsmul_eq_mul, AddCircle.coe_nsmul, coe_reprIco, ← map_nsmul, ← ofMul_pow,
        pow_card_eq_one, ofMul_one, map_zero]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h0
    rw [zsmul_one] at hn
    simp only [Set.mem_Ico] at hy01
    have hmpos : (0 : ℚ) < m := by exact_mod_cast (omega : 0 < m)
    have hn0 : 0 ≤ n := by
      have : (0 : ℚ) ≤ n := by rw [hn]; exact mul_nonneg hmpos.le hy01.1
      exact_mod_cast this
    have hnm : n < m := by
      have : (n : ℚ) < m := by rw [hn]; nlinarith
      exact_mod_cast this
    refine ⟨n.toNat, by omega, ?_⟩
    rw [← coe_reprIco (χ (Additive.ofMul x))]
    congr 1
    rw [show ((n.toNat : ℕ) : ℚ) = (n : ℚ) by exact_mod_cast Int.toNat_of_nonneg hn0, hn]
    field_simp
  choose k hkm hkeq using hk
  have hkinj : Function.Injective k := by
    intro x x' h
    apply Additive.ofMul.injective
    apply hχ
    rw [← hkeq x, ← hkeq x', h]
  have himage : Finset.univ.image k = Finset.range m := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hi
      exact Finset.mem_range.2 (hkm x)
    · rw [Finset.card_range, Finset.card_image_of_injective _ hkinj, Finset.card_univ]
  have h1 : 1 ∈ Finset.univ.image k := by
    rw [himage]
    exact Finset.mem_range.2 (by omega)
  obtain ⟨g, -, hg⟩ := Finset.mem_image.1 h1
  have hχg := hkeq g
  rw [hg, Nat.cast_one] at hχg
  have hord : orderOf g = m := by
    rw [← addOrderOf_ofMul_eq_orderOf, ← addOrderOf_injective χ hχ, ← hχg]
    exact AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (n := m) (by omega)
  exact isCyclic_of_orderOf_eq_card g (by rw [hord, Nat.card_eq_fintype_card])

end Cyclicity

section Kernel

variable {G : Type} [Group G]

def charComp (S : Subgroup G) [S.Normal] (ψ : Additive (G ⧸ S) →+ AddCircle (1 : ℚ)) :
    Additive G →+ AddCircle (1 : ℚ) :=
  ψ.comp (MonoidHom.toAdditive (QuotientGroup.mk' S))

def charKer (χ : Additive G →+ AddCircle (1 : ℚ)) : Subgroup G :=
  (AddMonoidHom.toMultiplicativeRight χ).ker

theorem mem_charKer {χ : Additive G →+ AddCircle (1 : ℚ)} {x : G} :
    x ∈ charKer χ ↔ χ (Additive.ofMul x) = 0 := by
  rw [charKer, MonoidHom.mem_ker, AddMonoidHom.toMultiplicativeRight_apply_apply, ofAdd_eq_one]

instance (χ : Additive G →+ AddCircle (1 : ℚ)) : (charKer χ).Normal :=
  MonoidHom.normal_ker _

def charBar (χ : Additive G →+ AddCircle (1 : ℚ)) :
    Additive (G ⧸ charKer χ) →+ AddCircle (1 : ℚ) :=
  MonoidHom.toAdditiveLeft (QuotientGroup.kerLift (AddMonoidHom.toMultiplicativeRight χ))

theorem charBar_apply (χ : Additive G →+ AddCircle (1 : ℚ)) (x : G) :
    charBar χ (Additive.ofMul (x : G ⧸ charKer χ)) = χ (Additive.ofMul x) :=
  rfl

theorem charBar_injective (χ : Additive G →+ AddCircle (1 : ℚ)) :
    Function.Injective (charBar χ) := by
  intro x y h
  apply Additive.toMul.injective
  apply QuotientGroup.kerLift_injective (AddMonoidHom.toMultiplicativeRight χ)
  exact congrArg Multiplicative.ofAdd h

theorem charComp_charBar (χ : Additive G →+ AddCircle (1 : ℚ)) :
    charComp (charKer χ) (charBar χ) = χ := by
  ext x
  exact charBar_apply χ (Additive.toMul x)

end Kernel

section Inflation

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

variable {G : Type} [Group G] {A : Rep ℤ G} (S : Subgroup G) [S.Normal]

def invariantsToQuotient (a : A.ρ.invariants) : (A.quotientToInvariants S).ρ.invariants :=
  ⟨⟨a, fun s => a.2 s⟩, fun q => by
    induction q using QuotientGroup.induction_on with
    | H g => exact Subtype.ext (a.2 g)⟩

end Inflation

end GroundTheory.ProfCoh
