module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

theorem finrank_relThree_add_finrank_twInv_le :
    ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G)
      (ρ : G → E →ₗ[ℂ] E) (t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) →
      t ^ 6 = 1 → FiniteDimensional ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) →
      FiniteDimensional ℂ (relThree Γ ρ t) ∧
        Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ (twInv Γ t (ρ t)) ≤
          Module.finrank ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) := by
  intro G _ E _ _ Γ ρ t hmul hone ht hfd
  have h2 : ∀ v, ρ (t ^ 2) v = ρ t (ρ t v) := fun v => by rw [pow_two, hmul]
  have h3 : ∀ v, ρ (t ^ 3) v = ρ t (ρ t (ρ t v)) := fun v => by
    rw [pow_succ t 2, hmul, h2]
  have h6 : ∀ v, ρ t (ρ t (ρ t (ρ t (ρ t (ρ t v))))) = v := fun v => by
    have h : t ^ 3 * t ^ 3 = 1 := by rw [← pow_add]; exact ht
    have h' := hmul (t ^ 3) (t ^ 3) v
    rw [h, hone, h3, h3] at h'
    exact h'.symm
  have e2 : ∀ x : G, x * t * t = x * t ^ 2 := fun x => by rw [pow_two, mul_assoc]
  have e3 : ∀ x : G, x * t * t ^ 2 = x * t ^ 3 := fun x => by
    rw [mul_assoc, ← pow_succ']
  have hle : relThree Γ ρ t ≤ twInv Γ (t ^ 3) (ρ (t ^ 3)) := fun Φ hΦ => hΦ.1
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  let P : twInv Γ (t ^ 3) (ρ (t ^ 3)) →ₗ[ℂ] twInv Γ t (ρ t) :=
    { toFun := fun Φ => ⟨fun x => ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2), by
        obtain ⟨Φ, hΓ, hΦ⟩ := Φ
        refine ⟨fun γ hγ x => ?_, fun x => ?_⟩
        · simp only [mul_assoc, hΓ γ hγ]
        · simp only [e2, e3, hΦ, h2, h3, map_add (f := _)]
          abel⟩
      map_add' := fun Φ Ψ => by
        ext x
        simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
        abel
      map_smul' := fun c Φ => by
        ext x
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply, smul_add] }
  have hP : ∀ Φ x, (P Φ).1 x = ρ (t ^ 2) (Φ.1 x) + ρ t (Φ.1 (x * t)) + Φ.1 (x * t ^ 2) :=
    fun _ _ => rfl
  have hsurj : LinearMap.range P = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨Ψ, hΓ, hΨ⟩
    have hΨ2 : ∀ x, Ψ (x * t ^ 2) = ρ t (ρ t (Ψ x)) := fun x => by rw [← e2, hΨ, hΨ]
    have hΨ3 : ∀ x, Ψ (x * t ^ 3) = ρ t (ρ t (ρ t (Ψ x))) := fun x => by rw [← e3, hΨ2, hΨ]
    refine ⟨⟨fun x => (1 / 3 : ℂ) • ρ t (ρ t (ρ t (ρ t (Ψ x)))), fun γ hγ x => ?_, fun x => ?_⟩, ?_⟩
    · simp only [hΓ γ hγ]
    · simp only [hΨ3, h3, map_smul]
    · ext x
      rw [hP]
      simp only [hΨ, hΨ2, h2, map_smul, h6]
      module
  have hker : Module.finrank ℂ (relThree Γ ρ t) ≤ Module.finrank ℂ (LinearMap.ker P) := by
    let ι : relThree Γ ρ t →ₗ[ℂ] LinearMap.ker P :=
      (Submodule.inclusion hle).codRestrict _ (fun Φ => by
        rw [LinearMap.mem_ker]
        ext x
        rw [hP]
        exact Φ.2.2 x)
    refine LinearMap.finrank_le_finrank_of_injective (f := ι) ?_
    intro a b hab
    exact Submodule.inclusion_injective hle (congrArg Subtype.val hab)
  have hrk := LinearMap.finrank_range_add_finrank_ker P
  rw [hsurj, finrank_top] at hrk
  omega

end GlobalTheory.HeckeFamilyMatrices.CocBound
