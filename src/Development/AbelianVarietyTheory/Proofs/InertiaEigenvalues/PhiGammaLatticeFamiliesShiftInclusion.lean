module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CloseVectorNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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

@[expose] public section

noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.CloseTw
open GlobalTheory.PhiGam.Close

theorem main : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (h : ZMod n → ℕ) (w : ZMod n → ℤ) (N₁ N₂ : Lats k n m), (∀ i, IsLat (N₁ i)) → (∀ i, IsLat (N₂ i)) → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₁ → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₂ → ∀ i, sh (sg l h i) (N₁ i) ≤ N₂ i := by
  intro k _ l n m hl _ _ R D h w N₁ N₂ h₁ h₂ c₁ c₂ i
  classical
  have hex : ∀ i, ∃ a : ℕ, ∀ x ∈ N₁ i, vv k ^ a • x ∈ N₂ i := fun i => exists_pow (h₁ i).1 (h₂ i).2
  have hrec : ∀ i, Nat.find (hex (i - 1)) ≤ (Nat.find (hex i) + h i) / l := by
    intro i
    refine Nat.find_min' _ fun x hx => ?_
    refine key hl.out.pos R (D.φ i) (D.φ_semi i) (D.etale i) _ (h₂ _) _ x ?_
    have e1 : vv k ^ (w i) • D.φ i x ∈ N₁ i := by
      have := mem_sh_iff_smul_mem.1 ((c₁ i).1 (Submodule.subset_span ⟨x, hx, rfl⟩))
      rwa [neg_neg] at this
    have e2 := (c₂ i).2 (mem_sh_iff_exists.2 ⟨_, Nat.find_spec (hex i) _ e1, rfl⟩)
    have hv := vv_ne_zero k
    rw [smul_smul, smul_smul, ← zpow_natCast, ← zpow_add₀ hv, ← zpow_add₀ hv] at e2
    rw [← zpow_natCast]
    convert e2 using 3
    push_cast
    ring
  have hle := le_sg hl.out.one_lt h (fun i => Nat.find (hex i)) (fun i => by
    have := hrec (i + 1)
    simp only [add_sub_cancel_right] at this
    exact (Nat.mul_le_mul_left l this).trans (Nat.mul_div_le _ _)) i
  exact sh_le fun x hx => pow_smul_mem hle (Nat.find_spec (hex i) x hx)

end GlobalTheory.PhiGam.CloseTw
