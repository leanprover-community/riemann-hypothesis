module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem pow_fix {G : Type} [Group G] (θ : Monoid.End G) (z : G) (hz : θ z = z) (m : ℕ) :
    (θ ^ m) z = z := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ_apply, hz, ih]

private theorem twNorm_central {G : Type} [Group G] (θ : Monoid.End G) (z : G) (hz : θ z = z)
    (hc : ∀ g, z * g = g * z) (m : ℕ) (δ : G) :
    twNorm θ m (z * δ) = z ^ m * twNorm θ m δ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [twNorm_succ, twNorm_succ, ih, map_mul, pow_fix θ z hz m, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc (twNorm θ m δ) z, ← hc (twNorm θ m δ), mul_assoc]

theorem UpperTheory.twistedNorm_central_of_baseChange_compat :
    Compat → CentLoc → CentBC → ZNorm := by
  intro hC hL hB F E _ _ _ _ _ _ σ _ n _ s δ
  have hl : (Module.finrank F E : ℝ) ≠ 0 := by
    have : 0 < Module.finrank F E := Module.finrank_pos
    exact_mod_cast this.ne'
  have c3 := (hC F E σ n).2.2.1
  have c6 := (hC F E σ n).2.2.2.2.2.1

  have e1 : (⟨Real.exp (s / Module.finrank F E), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) ^ Module.finrank F E
      = ⟨Real.exp s, Real.exp_pos s⟩ := by
    apply Subtype.ext
    have : ((⟨Real.exp (s / Module.finrank F E), Real.exp_pos _⟩ ^ Module.finrank F E : {r : ℝ // 0 < r}) : ℝ) = Real.exp (s / Module.finrank F E) ^ Module.finrank F E := rfl
    rw [this, ← Real.exp_nat_mul, mul_div_cancel₀ _ hl]
  have hz : pI E n (zA E n s) =
      mapGL n (infMap F E) (pI F n (zA F n (s / Module.finrank F E))) := by
    rw [← c3, hB F E n, e1]
  have hfix : mapGL n (galInf σ) (pI E n (zA E n s)) = pI E n (zA E n s) := by
    rw [hz]; exact c6 _
  have hcen := (hL E n ⟨Real.exp s, Real.exp_pos s⟩).2.1
  have hpow : pI E n (zA E n s) ^ Module.finrank F E =
      mapGL n (infMap F E) (pI F n (zA F n s)) := by
    rw [← c3, hB F E n, ← map_pow, ← map_pow]
  exact (twNorm_central (mapGL n (galInf σ)) _ hfix hcen _ δ).trans (by rw [hpow])
