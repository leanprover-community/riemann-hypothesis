module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.Columns.ChainTwCst
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT


open Classical in
theorem addChar_isIntegral {A : Type} [AddCommGroup A] [Finite A] {K : Type} [Field K] (ψ : AddChar A K) (y : A) :
    IsIntegral ℤ (ψ y) := by
  refine IsIntegral.of_pow (Nat.card_pos (α := A)) ?_
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  exact isIntegral_one

theorem qOf_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : 0 < qOf w := by
  refine Nat.pos_of_ne_zero ?_
  unfold qOf
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact w.ne_bot

theorem ciPsi_isIntegral {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (P : SB) (x : X.E) : IsIntegral ℤ (ciPsi Ch P x) := by
  classical
  unfold ciPsi
  split
  · have := ciFinite (X := X) (qOf_pos P.1).ne'
    exact addChar_isIntegral _ _
  · exact isIntegral_one

theorem twZeta_pow_eq_one {X : Fields} (σ₀ : X.K →+* ℂ) {N : ℕ} (hN : 0 < N)
    (hex : ∃ z : X.K, σ₀ z = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))) : twZeta σ₀ N ^ N = 1 := by
  have hs : σ₀ (twZeta σ₀ N) = Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) := Classical.epsilon_spec hex
  apply σ₀.injective
  rw [map_pow, hs, map_one, ← Complex.exp_nat_mul]
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show (N : ℂ) * (2 * Real.pi * Complex.I / (N : ℂ)) = 2 * Real.pi * Complex.I by field_simp]
  exact Complex.exp_two_pi_mul_I

theorem twPsiQ_isIntegral {X : Fields} (σ₀ : X.K →+* ℂ) (xi0 : X.E) (P : HeightOneSpectrum (𝓞 X.E)) (D : ℕ)
    (hz : twZeta σ₀ (qOf P ^ D) ^ (qOf P ^ D) = 1) (a : X.E) : IsIntegral ℤ (twPsiQ σ₀ xi0 P D a) := by
  classical
  unfold twPsiQ
  split
  · refine IsIntegral.of_pow (pow_pos (qOf_pos P) D) ?_
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hz, _root_.one_zpow]
    exact isIntegral_one
  · exact isIntegral_one

theorem psi_isIntegral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (a : I.ι) (P : SBof I a) (x : B.fields.E),
    IsIntegral ℤ ((I.cst a).psi P x) := by
  intro B X I h ht a P x
  rw [ht.cst_eq a]
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · rw [twCst_psi_g hP]
    exact ciPsi_isIntegral _ _ _
  · rw [twCst_psi_Q hP]
    exact twPsiQ_isIntegral _ _ _ _
      (twZeta_pow_eq_one _ (pow_pos (qOf_pos P.1) _) (TC.root_of_ok h ht.deep a P hP)) x

end GlobalTheory.Mem.Col2.AdT
