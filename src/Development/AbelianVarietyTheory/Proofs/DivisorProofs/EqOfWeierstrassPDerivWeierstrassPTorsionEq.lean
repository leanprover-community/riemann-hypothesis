module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembershipStatement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem wp_wpd_separate : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 →
    wp N x τ = wp N y τ → wpd N x τ = wpd N y τ → x = y := by
  intro N _ τ x y hx hy h1 h2
  obtain ⟨hsub, -, hmem, -, -⟩ := GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership N τ
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hz : tors N τ x ∉ (tauPair τ).lattice := fun h => hx ((hmem x).1 h)
  have hw : tors N τ y ∉ (tauPair τ).lattice := fun h => hy ((hmem y).1 h)
  rw [wp, wp, div_left_inj' (pow_ne_zero _ hc)] at h1
  rw [wpd, wpd, div_left_inj' (pow_ne_zero _ hc)] at h2
  rcases (Formalism.L2.Th1.F.pInjective (tauPair τ) _ _ hz hw).1 h1 with h | h
  · exact (hsub x y).1 h
  · apply (hsub x y).1
    have e : tors N τ x = -tors N τ y + ((⟨_, h⟩ : (tauPair τ).lattice) : ℂ) := by
      simp
    have h3 : (tauPair τ).derivWeierstrassP (tors N τ x) =
        -(tauPair τ).derivWeierstrassP (tors N τ y) := by
      conv_lhs => rw [e]
      rw [PeriodPair.derivWeierstrassP_add_coe, PeriodPair.derivWeierstrassP_neg]
    have h0 : (tauPair τ).derivWeierstrassP (tors N τ y) = 0 := by
      rw [h2] at h3
      linear_combination h3 / 2
    have h4 := (Formalism.L2.Th1.F.pDerivZero (tauPair τ) _ hw).1 h0
    have h5 := (tauPair τ).lattice.sub_mem h h4
    convert h5 using 1
    ring

end GlobalTheory.WpFam
