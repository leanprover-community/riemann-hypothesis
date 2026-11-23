module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqInvStabilizerVolumeStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HL
open scoped ENNReal Classical

namespace GlobalTheory.HL

theorem inv_encard_stab_ne {G : Type} [Group G] (Γ K0 : Subgroup G)
    (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) (y : G ⧸ K0) :
    ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ ≠ 0 ∧
    ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ ≠ ⊤ := by
  induction y using QuotientGroup.induction_on with
  | H g =>
    have hsub : ((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G) ⊆
        {γ | γ ∈ Γ ∧ g⁻¹ * γ * g ∈ K0} := by
      intro γ hγ
      simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hγ
      refine ⟨hγ.1, ?_⟩
      have h2 := hγ.2
      rw [MulAction.Quotient.smul_coe, QuotientGroup.eq] at h2
      have := K0.inv_mem h2
      simpa [mul_assoc] using this
    have hfin := (hF g).subset hsub
    have hne : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).Nonempty :=
      ⟨1, Subgroup.one_mem _⟩
    constructor
    · rw [ne_eq, ENNReal.inv_eq_zero]
      intro h
      have : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = ⊤ := by
        exact_mod_cast h
      exact (Set.encard_ne_top_iff.2 hfin) this
    · rw [ne_eq, ENNReal.inv_eq_top]
      intro h
      have : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = 0 := by
        exact_mod_cast h
      exact hne.ne_empty (Set.encard_eq_zero.1 this)

theorem mass_quotient_pos_finite {G : Type} [Group G] (Γ K0 : Subgroup G)
    (hS : ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ)
    (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) :
    (∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ K0),
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) ≠ 0 ∧
    (∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ K0),
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) ≠ ⊤ := by
  obtain ⟨S, hS⟩ := hS
  have hfin : Finite (MulAction.orbitRel.Quotient Γ (G ⧸ K0)) := by
    let f : S → MulAction.orbitRel.Quotient Γ (G ⧸ K0) := fun a =>
      Quotient.mk _ ((a.1 : G) : G ⧸ K0)
    refine Finite.of_surjective f ?_
    intro o
    induction o using Quotient.inductionOn with
    | h y =>
      induction y using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨a, ha, γ, hγ, κ, hκ, rfl⟩ := hS g
        refine ⟨⟨a, ha⟩, ?_⟩
        apply Quotient.sound
        refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
        show (γ⁻¹ : G) • ((γ * a * κ : G) : G ⧸ K0) = _
        rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
        simpa [mul_assoc] using K0.inv_mem hκ
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Γ (G ⧸ K0))
  constructor
  · rw [ne_eq, ENNReal.tsum_eq_zero, not_forall]
    exact ⟨Quotient.mk _ ((1 : G) : G ⧸ K0), (inv_encard_stab_ne Γ K0 hF _).1⟩
  · rw [tsum_fintype]
    exact ENNReal.sum_ne_top.2 (fun o _ => (inv_encard_stab_ne Γ K0 hF _).2)

theorem mass_orbit_eq_of_finite_double_cosets : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), (∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ) → (∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) → ∃ V0 : ℝ, 0 < V0 ∧ ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V0 * invVol K0 (MulAction.stabilizer G x)) := by
  intro G _ Γ K0 hS hF
  obtain ⟨V, hV⟩ := GlobalTheory.T.orbit_mass_eq_inv_stabilizer_volume Γ K0
  have hstab : MulAction.stabilizer G ((1 : G) : G ⧸ K0) = K0 := MulAction.stabilizer_quotient K0
  have h0 := hV (G ⧸ K0) ((1 : G) : G ⧸ K0) (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero)
    (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero)
  have horb : ∀ y : G ⧸ K0, y ∈ MulAction.orbit G ((1 : G) : G ⧸ K0) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨g, show g • ((1 : G) : G ⧸ K0) = g by rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]⟩
  simp only [horb, ite_true, hstab] at h0
  rw [show invVol K0 K0 = 1 by simp [invVol, Subgroup.relIndex_self], ENNReal.ofReal_one,
    mul_one] at h0
  obtain ⟨hV0, hVt⟩ := mass_quotient_pos_finite Γ K0 hS hF
  have hV0' : V ≠ 0 := by rw [← h0]; exact hV0
  have hVt' : V ≠ ⊤ := by rw [← h0]; exact hVt
  refine ⟨V.toReal, ENNReal.toReal_pos hV0' hVt', fun X _ x h1 h2 => ?_⟩
  rw [hV X x h1 h2, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hVt']

end GlobalTheory.HL
