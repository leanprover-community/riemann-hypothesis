module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.ContinuousPhi
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.IntegralHkDiag
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.FFTSteps.PosProof

variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]

theorem gw_prod (z : Sg ι A B → ℂ) : Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, e1 (z s) := by
  simp only [e1]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp [Finset.sum_neg_distrib]

def mon (m : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) : ℂ := ∏ s, z s ^ m s

theorem mon_prod (m m' : Sg ι A B →₀ ℕ) (z : Sg ι A B → ℂ) :
    mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = ∏ s, hk (m s) (m' s) (z s) := by
  rw [gw_prod]
  simp only [mon, hk, Complex.star_def, map_prod, map_pow, Finset.prod_mul_distrib]

theorem integrable_mon (m m' : Sg ι A B →₀ ℕ) :
    Integrable (fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
  simp_rw [mon_prod]
  have := Integrable.fintype_prod (f := fun s => hk (m s) (m' s)) (μ := fun _ => (volume : Measure ℂ))
    (fun s => integrable_hk _ _)
  rwa [← volume_pi] at this

theorem integral_mon (m m' : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ∏ s, ∫ w, hk (m s) (m' s) w := by
  simp_rw [mon_prod]
  exact integral_fintype_prod_volume_eq_prod (fun s w => hk (m s) (m' s) w)

theorem integral_mon_ne (m m' : Sg ι A B →₀ ℕ) (h : m ≠ m') :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) = 0 := by
  rw [integral_mon]
  obtain ⟨s, hs⟩ : ∃ s, m s ≠ m' s := by
    by_contra hc
    push Not at hc
    exact h (Finsupp.ext hc)
  exact Finset.prod_eq_zero (Finset.mem_univ s) (integral_hk_ne _ _ hs)

theorem integral_mon_self (m : Sg ι A B →₀ ℕ) :
    ∫ z : Sg ι A B → ℂ, mon m z * star (mon m z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
      ((∏ s, jr (m s) : ℝ) : ℂ) := by
  rw [integral_mon]
  push_cast
  exact Finset.prod_congr rfl fun s _ => integral_hk_diag _

def kap (d : ι → ℝ) : Sg ι A B → ℝ := Sum.elim (fun _ => 1) (fun y => d y.1)

def lam (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) : ℝ := ∏ s, kap d s ^ m s

theorem Phi_diag (d : ι → ℝ) (z : Sg ι A B → ℂ) :
    Phi (Matrix.diagonal fun i => (d i : ℂ)) z = fun s => (kap d s : ℂ) * z s := by
  funext s
  rcases s with x | ⟨i, b⟩
  · simp [Phi, kap]
  · simp [Phi, kap, Matrix.diagonal_apply]

theorem gip_diag (d : ι → ℝ) (g : PV ι A B) :
    gip (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) g =
      ((∑ m ∈ g.support, Complex.normSq (g.coeff m) * lam d m * ∏ s, jr (m s) : ℝ) : ℂ) := by
  unfold gip
  have hpt : ∀ z : Sg ι A B → ℂ,
      eval z (sub 1 (Matrix.diagonal fun i => (d i : ℂ)) g) * star (eval z g) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) =
        ∑ m ∈ g.support, ∑ m' ∈ g.support, (g.coeff m * (lam d m : ℂ) * star (g.coeff m')) *
          (mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ))) := by
    intro z
    rw [eval_sub, Phi_diag, MvPolynomial.eval_eq', MvPolynomial.eval_eq']
    have hl : ∀ m : Sg ι A B →₀ ℕ, ∏ s, ((kap d s : ℂ) * z s) ^ m s = (lam d m : ℂ) * mon m z := by
      intro m
      simp only [mul_pow, Finset.prod_mul_distrib, lam, mon]
      push_cast
      rfl
    simp_rw [hl]
    rw [star_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m' _ => ?_
    have hmon : (∏ i, z i ^ m' i) = mon m' z := rfl
    try simp only [star_mul']
    try rw [hmon]
    ring
  simp_rw [hpt]
  have hint : ∀ m m' : Sg ι A B →₀ ℕ, Integrable fun z : Sg ι A B → ℂ => mon m z * star (mon m' z) * Complex.exp (-(∑ s, ‖z s‖ ^ 2 : ℝ)) :=
    integrable_mon
  rw [MeasureTheory.integral_finsetSum _ fun m _ => MeasureTheory.integrable_finsetSum _ fun m' _ => (hint m m').const_mul _]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MeasureTheory.integral_finsetSum _ fun m' _ => (hint m m').const_mul _]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single_of_mem m hm fun m' _ hne => by rw [integral_mon_ne m m' hne.symm, mul_zero]]
  rw [integral_mon_self]
  have hc : ((Complex.normSq (g.coeff m) : ℝ) : ℂ) = g.coeff m * star (g.coeff m) := by
    rw [Complex.star_def, Complex.mul_conj]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, hc]
  ring

end PositivityTheory.Rg.Sw.FFTSteps.PosProof
