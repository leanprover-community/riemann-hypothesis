module

import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.TriSupportedLe
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial

namespace CompanionTheory.Groth.ChartWirtingerDerivatives

def toZAlg {σ : Type*} (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  AlgHom.mk ψ (by
    intro r
    show ψ (algebraMap ℤ (MvPolynomial σ ℤ) r) = algebraMap ℤ (MvPolynomial σ ℤ) r
    rw [algebraMap_eq, eq_intCast C r]
    exact map_intCast ψ r)

theorem tri_supported_le {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) (N : ℕ) :
    supported ℤ {t | w t < N} ≤ (supported ℤ {t | w t < N}).map (toZAlg ψ) := by
  induction N with
  | zero =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    exact absurd ht (by simp)
  | succ N ih =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_ofPred_eq] at ht
    have hmono : (supported ℤ {t | w t < N}).map (toZAlg ψ) ≤
        (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.map_mono (supported_mono fun t (ht : w t < N) => (Nat.lt_succ_of_lt ht : w t < N + 1))
    obtain ⟨ε, p, hp, hψ⟩ := h t
    have hpmem : p ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) := by
      apply hmono; apply ih
      rw [mem_supported]
      intro u hu
      have := hp u hu
      simp only [Set.mem_ofPred_eq]; omega
    have hXmem : ψ (X t) ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.mem_map.2 ⟨X t, (X_mem_supported).2 (by simpa using ht), rfl⟩
    have heq : (X t : MvPolynomial σ ℤ) = (ε : ℤ) • ψ (X t) - (ε : ℤ) • p := by
      rw [hψ, smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, add_sub_cancel_right]
    rw [SetLike.mem_coe, heq]
    exact Subalgebra.sub_mem _ (Subalgebra.smul_mem _ hXmem _) (Subalgebra.smul_mem _ hpmem _)

theorem tri_surj {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Surjective ψ := by
  intro y
  have hy : y ∈ supported ℤ {t | w t < y.vars.sup (fun t => w t + 1)} := by
    rw [mem_supported]
    intro t ht
    have := Finset.le_sup (f := fun t => w t + 1) (Finset.mem_coe.1 ht)
    simp only [Set.mem_ofPred_eq]; omega
  obtain ⟨x, -, hx⟩ := Subalgebra.mem_map.1 (tri_supported_le w ψ h _ hy)
  exact ⟨x, hx⟩

theorem tri_bij {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Bijective ψ := by
  apply PositivityTheory.Groth.ChartWirtingerDerivatives.tri_bij <;> assumption

theorem uni_inj {M I : Type*} (L : M ≃ I) (w : M → ℕ) (f : M → I →₀ ℤ)
    (h1 : ∀ m, f m (L m) = 1) (hlt : ∀ m n, f m (L n) ≠ 0 → m = n ∨ w m < w n) :
    Function.Injective (Finsupp.linearCombination ℤ f) := by
  apply PositivityTheory.Groth.ChartWirtingerDerivatives.uni_inj <;> assumption

theorem uni_exists {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    ∀ n, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 := by
  apply PositivityTheory.Groth.ChartWirtingerDerivatives.uni_exists <;> assumption

theorem uni_bij {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    Function.Bijective (Finsupp.linearCombination ℤ f) := by
  refine ⟨uni_inj L w f h1 fun m n h => (hlt m n h).2, ?_⟩
  intro y
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · exact ⟨0, map_zero _⟩
  · rintro y z ⟨a, ha⟩ ⟨a', ha'⟩
    exact ⟨a + a', by rw [map_add (f := _), ha, ha']⟩
  · intro i r
    obtain ⟨a, -, ha⟩ := uni_exists L c w b f hb h1 hlt (L.symm i)
    exact ⟨r • a, by rw [map_smul, ha, L.apply_symm_apply, Finsupp.smul_single_one]⟩

end CompanionTheory.Groth.ChartWirtingerDerivatives

namespace CompanionTheory.Groth

theorem triAut : TriAut := fun _ w ψ h => ChartWirtingerDerivatives.tri_bij w ψ h

theorem uniTri : UniTri := fun _ _ _ L c w b f hb h1 hlt =>
  ⟨ChartWirtingerDerivatives.uni_bij L c w b f hb h1 hlt, ChartWirtingerDerivatives.uni_exists L c w b f hb h1 hlt⟩

end CompanionTheory.Groth
