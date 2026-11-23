module

public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeightedDoubleCoset

def stabConjEquiv {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Unfold.stab Γ K ((γ₀ : G) * g * k) ≃ Unfold.stab Γ K g where
  toFun δ := ⟨γ₀⁻¹ * δ.1 * γ₀, by
    have h := K.mul_mem (K.mul_mem k.2 δ.2) (K.inv_mem k.2)
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  invFun δ := ⟨γ₀ * δ.1 * γ₀⁻¹, by
    have h := K.mul_mem (K.mul_mem (K.inv_mem k.2) δ.2) k.2
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  left_inv δ := by ext; simp [mul_assoc]
  right_inv δ := by ext; simp [mul_assoc]

theorem card_stab_eq {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Nat.card (Unfold.stab Γ K ((γ₀ : G) * g * k)) = Nat.card (Unfold.stab Γ K g) :=
  Nat.card_congr (stabConjEquiv Γ K g γ₀ k)

theorem sum_inv_card_stab_eq : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (n m : ℕ) (g : Fin n → G) (g' : Fin m → G), (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) → (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g' i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g' i * k = (γ' : G) * g' j * k' → i = j) → ∑ i, ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ∑ j, ((Nat.card (Unfold.stab Γ K (g' j)) : ℝ))⁻¹ := by
  intro G _ Γ K n m g g' hcov hdisj hcov' hdisj'
  choose e γe ke he using fun i => hcov' (g i)
  choose f γf kf hf using fun j => hcov (g' j)
  have hfe : ∀ i, f (e i) = i := by
    intro i
    symm
    refine hdisj i (f (e i)) 1 (γe i * γf (e i)) 1 (kf (e i) * ke i) ?_
    have h1 := he i
    rw [hf (e i)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  have hef : ∀ j, e (f j) = j := by
    intro j
    symm
    refine hdisj' j (e (f j)) 1 (γf j * γe (f j)) 1 (ke (f j) * kf j) ?_
    have h1 := hf j
    rw [he (f j)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  let σ : Fin n ≃ Fin m := ⟨e, f, hfe, hef⟩
  refine Fintype.sum_equiv σ _ _ (fun i => ?_)
  show ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ((Nat.card (Unfold.stab Γ K (g' (e i))) : ℝ))⁻¹
  rw [he i, card_stab_eq]

end GlobalTheory.WeightedDoubleCoset
