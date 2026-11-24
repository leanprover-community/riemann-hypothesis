module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
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

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem frobenius_symm_smul {p : ℕ} {A C : Type} [CommRing A] [CommRing C] [Algebra A C]
    (FA : A ≃+* A) (hFA : ∀ x, FA x = x ^ p) (FC : C ≃+* C) (hFC : ∀ x, FC x = x ^ p)
    (a : A) (c : C) : FC.symm (a • c) = FA.symm a • FC.symm c := by
  apply FC.injective
  rw [RingEquiv.apply_symm_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
    RingEquiv.apply_symm_apply, hFC, ← map_pow (algebraMap A C), ← hFA (FA.symm a),
    RingEquiv.apply_symm_apply]

private theorem exists_ringEquiv_frobenius_of_pf (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (h : Pf p A) :
    ∃ F : A ≃+* A, ∀ x, F x = x ^ p := by
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p A h.char 1
  have hg' : ∀ x, g x = x ^ p := fun x => by rw [hg, pow_one]
  have hb : Function.Bijective g := by
    have e : (g : A → A) = fun x => x ^ p := funext hg'
    rw [e]
    exact h.bij
  exact ⟨RingEquiv.ofBijective g hb, fun x => by rw [RingEquiv.ofBijective_apply, hg']⟩

theorem pf_tensor : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (B : Type) [CommRing B]
    [Algebra A B] (K : Type) [CommRing K] [Algebra A K], Pf p A → Pf p B → Pf p K →
    Pf p (B ⊗[A] K) := by
  intro p _ A _ B _ _ K _ _ hA hB hK
  obtain ⟨FA, hFA⟩ := exists_ringEquiv_frobenius_of_pf p A hA
  obtain ⟨FB, hFB⟩ := exists_ringEquiv_frobenius_of_pf p B hB
  obtain ⟨FK, hFK⟩ := exists_ringEquiv_frobenius_of_pf p K hK
  have hchar : (p : B ⊗[A] K) = 0 := by
    have h := map_natCast (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] K) p
    rw [← h, hB.char, map_zero]
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p (B ⊗[A] K) hchar 1
  have hg' : ∀ x, g x = x ^ p := fun x => by rw [hg, pow_one]
  let f : B →+ K →+ B ⊗[A] K :=
    AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun k => FB.symm b ⊗ₜ[A] FK.symm k)
      (fun k k' => by rw [map_add (f := _), TensorProduct.tmul_add]))
      (fun b b' => by
        ext k
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add (f := _), TensorProduct.add_tmul])
  have hf : ∀ (a : A) (b : B) (k : K), f (a • b) k = f b (a • k) := by
    intro a b k
    simp only [f, AddMonoidHom.mk'_apply]
    rw [frobenius_symm_smul FA hFA FB hFB, frobenius_symm_smul FA hFA FK hFK, TensorProduct.smul_tmul]
  have hψ : ∀ x, TensorProduct.liftAddHom f hf (g x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b k =>
      rw [hg', Algebra.TensorProduct.tmul_pow, TensorProduct.liftAddHom_tmul]
      simp only [f, AddMonoidHom.mk'_apply]
      rw [← hFB b, ← hFK k, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hgfun : (fun x : B ⊗[A] K => x ^ p) = g := funext fun x => (hg' x).symm
  refine ⟨hchar, ?_⟩
  rw [hgfun]
  refine ⟨Function.LeftInverse.injective hψ, ?_⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero g⟩
  | tmul b k =>
    obtain ⟨b', hb'⟩ := hB.bij.2 b
    obtain ⟨k', hk'⟩ := hK.bij.2 k
    have hb'' : b' ^ p = b := hb'
    have hk'' : k' ^ p = k := hk'
    refine ⟨b' ⊗ₜ[A] k', ?_⟩
    rw [hg', Algebra.TensorProduct.tmul_pow, hb'', hk'']
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add (f := _), hx', hy']⟩

end GlobalTheory.CompanionTheory.PerfectRing
