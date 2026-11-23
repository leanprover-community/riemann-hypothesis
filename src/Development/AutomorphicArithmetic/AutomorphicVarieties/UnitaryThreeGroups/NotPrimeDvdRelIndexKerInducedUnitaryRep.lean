module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnitaryThreeReflectionRight
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

theorem UpperTheory.not_prime_dvd_relIndex_ker_inducedUnitaryRep :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l], l ≠ 2 → ∀ {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* kˣ) (I : Subgroup Γ),
          ¬ l ∣ (I ⊓ (r0 η Ψ).ker).relIndex I := by
  intro l _ k _ _ _ hl2 Γ _ η Ψ I
  haveI := Fintype.ofFinite k
  have hp : l.Prime := Fact.out
  obtain ⟨n, -, hcard⟩ := FiniteField.card k l
  let φ : Γ →* kˣ × ℤˣ := Ψ.prod η
  let ψ : kˣ × ℤˣ →* GG (m := 3) (R := k) := r0 (MonoidHom.snd kˣ ℤˣ) (MonoidHom.fst kˣ ℤˣ)
  have hle : (φ.domRestrict I).ker ≤ ((r0 η Ψ).domRestrict I).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    show ψ (φ.domRestrict I g) = 1
    rw [hg, map_one]
  have h1 : (I ⊓ (r0 η Ψ).ker).relIndex I ∣ (φ.domRestrict I).ker.index := by
    rw [inf_comm, Subgroup.inf_relIndex_right, Subgroup.relIndex, ← MonoidHom.ker_restrict]
    exact Subgroup.index_dvd_of_le hle
  have h2 : (φ.domRestrict I).ker.index ∣ (Nat.card k - 1) * 2 := by
    rw [Subgroup.index_ker]
    have hd := Subgroup.card_subgroup_dvd_card (φ.domRestrict I).range
    rwa [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card (α := ℤˣ),
      Fintype.card_units_int] at hd
  rw [Nat.card_eq_fintype_card, hcard] at h2
  intro hdvd
  have h3 := dvd_trans hdvd (dvd_trans h1 h2)
  rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
  · have h5 : l ∣ l ^ (n : ℕ) := dvd_pow_self l n.ne_zero
    have hpos : 1 ≤ l ^ (n : ℕ) := Nat.one_le_pow _ _ hp.pos
    have he : l ^ (n : ℕ) = (l ^ (n : ℕ) - 1) + 1 := by omega
    rw [he] at h5
    have h6 := (Nat.dvd_add_right h4).mp h5
    exact hp.one_lt.ne' (Nat.dvd_one.mp h6)
  · have h7 := Nat.le_of_dvd (by norm_num) h4
    have h8 := hp.two_le
    omega
