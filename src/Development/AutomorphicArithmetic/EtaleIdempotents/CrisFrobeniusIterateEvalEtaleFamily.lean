module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct GlobalTheory.LogCris DividedPowers UpperTheory.Ru.crystallineComparison

private theorem iter_gen {A R ι : Type*} (f : A → A) (φ : R → R) (E : (ι → R) → A)
    (h : ∀ c, f (E c) = E (fun k => φ (c k))) (N : ℕ) (c : ι → R) :
    f^[N] (E c) = E (fun k => φ^[N] (c k)) := by
  induction N generalizing c with
  | zero => rfl
  | succ N ih =>
    simp only [Function.iterate_succ_apply]
    rw [h, ih]

private theorem sl_sum {R A ι : Type*} [Semiring R] [AddCommMonoid A] [Module R A] (σ : R →+* R)
    (f : A →ₛₗ[σ] A) [Fintype ι] (c : ι → R) (x : ι → A) (hx : ∀ k, f (x k) = x k) :
    f (∑ k, c k • x k) = ∑ k, σ (c k) • x k := by

  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [LinearMap.map_smulₛₗ, hx]

theorem UpperTheory.crisFrobenius_iterate_evalEtaleFamily :
    ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (e : E.EtFam l K), e.Phi → ∀ (M : Model l K) (j n N : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l),
        (phiH M.P n j)^[N] (evE e M j n v c) = evE e M j n v (fun k => (phiA l)^[N] (c k)) := by
  intro l _ K e he M j n N ι _ v c
  exact iter_gen (phiH M.P n j) (phiA l) (fun c => evE e M j n v c)
    (fun c => sl_sum (ACris.phi (K := ℂ_[l]) (p := l)) (M.phiMH n j) c (fun k => e M n j ((v k).lev n))
      (fun k => he M n j _)) N c
