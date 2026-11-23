module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

namespace UpperTheory

set_option backward.isDefEq.respectTransparency false in
private theorem hb_step {C : Type*} [Category C] [Preadditive C] (K D : CochainComplex C ℤ)
    (H : ∀ (p j : ℤ) (f : K.X p ⟶ D.X j), f ≫ D.d j (j + 1) = 0 →
      ∃ g : K.X p ⟶ D.X (j - 1), g ≫ D.d (j - 1) j = f)
    (n p₀ : ℤ) (z : Cochain K D n) (hz : δ n (n + 1) z = 0)
    (hv : ∀ (p q : ℤ) (hpq : p + n = q), p₀ < p → z.v p q hpq = 0) :
    ∃ γ : Cochain K D (n - 1), ∀ (p q : ℤ) (hpq : p + n = q), p₀ ≤ p →
      (z - δ (n - 1) n γ).v p q hpq = 0 := by
  have hf : z.v p₀ (p₀ + n) rfl ≫ D.d (p₀ + n) (p₀ + n + 1) = 0 := by
    have h0 := congrArg (fun c => Cochain.v c p₀ (p₀ + n + 1) (by omega)) hz
    simp only [Cochain.zero_v] at h0
    rw [δ_v n (n + 1) rfl z p₀ (p₀ + n + 1) (by omega) (p₀ + n) (p₀ + 1) (by omega) rfl,
      hv (p₀ + 1) (p₀ + n + 1) (by omega) (by omega), comp_zero, smul_zero, add_zero] at h0
    exact h0
  obtain ⟨g, hg⟩ := H p₀ (p₀ + n) (z.v p₀ (p₀ + n) rfl) hf
  refine ⟨Cochain.single g (n - 1), ?_⟩
  intro p q hpq hp
  rw [Cochain.sub_v, δ_v (n - 1) n (by omega) _ p q hpq (q - 1) (p + 1) rfl rfl,
    Cochain.single_v_eq_zero g (n - 1) (p + 1) q (by omega) (by omega), comp_zero, smul_zero, add_zero]
  rcases hp.lt_or_eq with hlt | rfl
  · rw [hv p q hpq hlt, Cochain.single_v_eq_zero g (n - 1) p (q - 1) (by omega) (by omega), zero_comp,
      sub_zero]
  · subst hpq
    rw [Cochain.single_v, hg, sub_self]

end UpperTheory

theorem UpperTheory.subsingleton_cohomologyClass_of_bounded_of_cycles_lift :
    ∀ (K D : Cx ℤ) [K.IsStrictlyLE 0] (a : ℤ) [D.IsStrictlyGE a], (∀ (p j : ℤ) (f : K.X p ⟶ D.X j), f ≫ D.d j (j + 1) = 0 → ∃ g : K.X p ⟶ D.X (j - 1), g ≫ D.d (j - 1) j = f) → ∀ n : ℤ, Subsingleton (CohomologyClass K D n) := by
  intro K D _ a _ H n
  have hz0 : ∀ (z : Cocycle K D n) (k : ℕ), ∃ γ : Cochain K D (n - 1), ∀ (p q : ℤ) (hpq : p + n = q),
      -(k : ℤ) < p → ((z : Cochain K D n) - δ (n - 1) n γ).v p q hpq = 0 := by
    intro z k
    induction k with
    | zero =>
      refine ⟨0, fun p q hpq hp => ?_⟩
      exact (K.isZero_of_isStrictlyLE 0 p (by simpa using hp)).eq_of_src _ _
    | succ k ih =>
      obtain ⟨γ, hγ⟩ := ih
      obtain ⟨γ', hγ'⟩ := UpperTheory.hb_step K D H n (-(k : ℤ)) ((z : Cochain K D n) - δ (n - 1) n γ)
        (by rw [δ_sub, z.δ_eq_zero, δ_δ, sub_zero]) (fun p q hpq hp => hγ p q hpq hp)
      refine ⟨γ + γ', fun p q hpq hp => ?_⟩
      rw [δ_add, ← sub_sub]
      exact hγ' p q hpq (by push_cast at hp; omega)
  have all : ∀ z : Cocycle K D n, CohomologyClass.mk z = 0 := by
    intro z
    obtain ⟨γ, hγ⟩ := hz0 z (n - a + 1).toNat
    have hk := Int.self_le_toNat (n - a + 1)
    have hzero : (z : Cochain K D n) - δ (n - 1) n γ = 0 := by
      apply Cochain.ext
      intro p q hpq
      rw [Cochain.zero_v]
      by_cases hp : -((n - a + 1).toNat : ℤ) < p
      · exact hγ p q hpq hp
      · exact (D.isZero_of_isStrictlyGE a q (by omega)).eq_of_tgt _ _
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n - 1, by omega, γ, (sub_eq_zero.mp hzero).symm⟩
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
  rw [all x, all y]
