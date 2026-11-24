module

public import Mathlib.Algebra.Module.Torsion.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem natCard_torsion_quot_span_dvd_of_range_subset :
    ∀ (L : Type) [AddCommGroup L] {m n : ℕ} (δ : Fin m → L) (γ : Fin n → L), LinearIndependent ℤ δ →
    Set.range γ ⊆ Set.range δ →
    Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ))) ∣
      Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ))) := by
  intro L _ m n δ γ hli hsub
  have hAB : Submodule.span ℤ (Set.range γ) ≤ Submodule.span ℤ (Set.range δ) :=
    Submodule.span_mono hsub
  have key : ∀ z : L, z ∈ Submodule.span ℤ (Set.range δ) → ∀ a : ℤ, a ≠ 0 →
      a • z ∈ Submodule.span ℤ (Set.range γ) → z ∈ Submodule.span ℤ (Set.range γ) := by
    intro z hz a ha haz
    have himg : δ '' (δ ⁻¹' Set.range γ) = Set.range γ := Set.image_preimage_eq_of_subset hsub
    rw [← himg] at haz ⊢
    rw [Finsupp.mem_span_image_iff_linearCombination] at haz ⊢
    obtain ⟨l', hl'S, hl'⟩ := haz
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz
    obtain ⟨c, hc⟩ := hz
    have hlc : Finsupp.linearCombination ℤ δ c = z := by
      rw [Finsupp.linearCombination_apply]; exact hc
    have heq : a • c = l' := by
      apply hli
      rw [map_smul, hlc, hl']
    refine ⟨c, ?_, hlc⟩
    rw [Finsupp.mem_supported'] at hl'S ⊢
    intro i hi
    have := hl'S i hi
    rw [← heq, Finsupp.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this).resolve_left ha
  let q : (L ⧸ Submodule.span ℤ (Set.range γ)) →ₗ[ℤ] (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    Submodule.factor hAB
  let f : Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range γ)) →+
      Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range δ)) :=
    (q.restrict (p := Submodule.torsion ℤ _) (q := Submodule.torsion ℤ _) (fun x hx => by
      rw [Submodule.mem_torsion_iff] at hx ⊢
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [Submonoid.smul_def] at ha ⊢; rw [← map_smul, ha, map_zero]⟩)).toAddMonoidHom
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ hfx
    have hqx : q x = 0 := congrArg Subtype.val hfx
    apply Subtype.ext
    simp only [ZeroMemClass.coe_zero]
    induction x using Submodule.Quotient.induction_on with
    | H z =>
      rw [Submodule.mem_torsion_iff] at hx
      obtain ⟨⟨a, ha0⟩, ha⟩ := hx
      have hz : z ∈ Submodule.span ℤ (Set.range δ) := by
        rw [← Submodule.Quotient.mk_eq_zero]
        simpa [q] using hqx
      have ha' : a ≠ 0 := nonZeroDivisors.ne_zero ha0
      have haz : a • z ∈ Submodule.span ℤ (Set.range γ) := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
        simpa [Submonoid.smul_def] using ha
      rw [Submodule.Quotient.mk_eq_zero]
      exact key z hz a ha' haz
  exact AddSubgroup.card_dvd_of_injective f hinj

end GlobalTheory
