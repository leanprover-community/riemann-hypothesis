module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtChart
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartLocalizationFiniteTypeFormallyUnramifiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedAStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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

open IsLocalRing

namespace GlobalTheory.DenseSec
open TensorProduct

theorem exists_poly_vanishing_of_fibre : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := by
  intro R _ A _ _ g t h hE Ω _ _ hirr f hf
  have hN : (nilradical (TensorProduct R Ω A)).IsPrime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 hirr
  have kill : ∀ (a : A →ₐ[R] Ω) (x : TensorProduct R Ω A), x ∈ nilradical (TensorProduct R Ω A) → GlobalTheory.DenseSec.pt a x = 0 := by
    intro a x hx
    exact ((mem_nilradical.1 hx).map (GlobalTheory.DenseSec.pt a)).eq_zero
  have pth : ∀ (a : A →ₐ[R] Ω) (x : A), GlobalTheory.DenseSec.pt a (1 ⊗ₜ[R] x) = a x := by
    intro a x
    simp [GlobalTheory.DenseSec.pt]
  have ptw : ∀ (a : A →ₐ[R] Ω) (w : Ω), GlobalTheory.DenseSec.pt a (w ⊗ₜ[R] 1) = w := by
    intro a w
    simp [GlobalTheory.DenseSec.pt]
  by_cases h1 : (1 ⊗ₜ[R] h : TensorProduct R Ω A) ∈ nilradical (TensorProduct R Ω A)
  · refine ⟨1, one_ne_zero, fun a ha _ => ?_⟩
    exact absurd (by rw [← pth a h]; exact kill a _ h1) ha
  set N := nilradical (TensorProduct R Ω A)
  set u : TensorProduct R Ω A ⧸ N := Ideal.Quotient.mk N (1 ⊗ₜ[R] h)
  have hu : u ≠ 0 := by
    simpa [u, Ideal.Quotient.eq_zero_iff_mem] using h1
  letI : IsDomain (TensorProduct R Ω A ⧸ N) := Ideal.Quotient.isDomain N
  have hle : Submonoid.powers u ≤ nonZeroDivisors (TensorProduct R Ω A ⧸ N) := powers_le_nonZeroDivisors_of_noZeroDivisors hu
  letI : IsDomain (Localization.Away u) := IsLocalization.isDomain_localization hle
  obtain ⟨hFT, hFU⟩ := GlobalTheory.T.etaleChart_localization_finiteType_formallyUnramified R A g t h hE Ω N
  letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away u) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  have hf' : algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N f) ≠ 0 := by
    intro h0
    rw [map_eq_zero_iff _ (IsLocalization.injective (Localization.Away u) hle), Ideal.Quotient.eq_zero_iff_mem] at h0
    exact hf (mem_nilradical.1 h0)
  obtain ⟨Q, hQ, d, hd⟩ := GlobalTheory.T.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified' (MvPolynomial (Fin g) Ω) (Localization.Away u) _ hf'
  refine ⟨Q, hQ, fun a ha hfa => ?_⟩
  let φ : TensorProduct R Ω A ⧸ N →+* Ω := Ideal.Quotient.lift N (GlobalTheory.DenseSec.pt a).toRingHom (fun x hx => kill a x hx)
  have hφu : IsUnit (φ u) := by
    simp only [φ, u, Ideal.Quotient.lift_mk]
    exact isUnit_iff_ne_zero.2 (by simpa [pth] using ha)
  let χ : Localization.Away u →+* Ω := IsLocalization.Away.lift u hφu
  have hχ : ∀ x : TensorProduct R Ω A, χ (algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N x)) = GlobalTheory.DenseSec.pt a x := by
    intro x
    simp [χ, φ, IsLocalization.Away.lift]
  have hP : χ.comp (algebraMap (MvPolynomial (Fin g) Ω) (Localization.Away u)) = MvPolynomial.eval₂Hom (RingHom.id Ω) (fun i => a (t i)) := by
    apply MvPolynomial.ringHom_ext
    · intro w
      show χ (MvPolynomial.aeval _ (MvPolynomial.C w)) = _
      have e : algebraMap Ω (TensorProduct R Ω A ⧸ N) w = Ideal.Quotient.mk N (w ⊗ₜ[R] 1) := rfl
      rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply Ω (TensorProduct R Ω A ⧸ N) (Localization.Away u), e, hχ, ptw]
      simp
    · intro i
      show χ (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, hχ, pth]
      simp
  have := congrArg χ hd
  rw [← RingHom.comp_apply, hP, map_mul, hχ, hfa, zero_mul] at this
  exact this

end GlobalTheory.DenseSec
