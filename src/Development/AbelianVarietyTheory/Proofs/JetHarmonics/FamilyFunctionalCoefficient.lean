module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsKTypeNonzeroBessel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_coef_family : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (s₀ : ℂ), IsFam lam q0 R → (haveI := FiniteDimensional.complete ℂ Wp; SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg) → (haveI := FiniteDimensional.complete ℂ Wq; SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg) → IsCoef (R 0) (l 0) (l' 0) f s₀ → s₀ ≠ 0 → ∃ (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (t : ℝ), 0 < t ∧ J 0 = (fun g => (t : ℂ) • f g) ∧ (NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0)) ∧ (∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν) ∧ (∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0) := by
  intro hH P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg f s₀ hfam hL hR hf hs₀
  haveI := FiniteDimensional.complete ℂ Wp
  haveI := FiniteDimensional.complete ℂ Wq
  classical
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have h0 : n1 (0 : Fin (2 * P.r + P.k + 1) → ℤ) ≤ q0 := by simp [n1]
  have hDS : ∀ ν, n1 ν ≤ q0 → (R ν).IsDS (PI.BesselPeriodGGP.eps48 P.k P.r) (fun a => lam a + (ν a : ℝ)) :=
    fun ν hν => hfam ν hν
  have hdg0 : 0 < dg 0 := (hL 0 h0).2.1
  have hsn : 0 < ‖s₀‖ := norm_pos_iff.mpr hs₀
  have hnz : NzOn (R 0) (l 0) ∧ NzOn (R 0) (l' 0) := by
    obtain ⟨m, x, y, X, hxy, -, hs⟩ := hf
    have hsm := (GlobalTheory.rep_basic_of_isDS hK _ _ _ _ (R 0) (hDS 0 h0)).2.2.2.2.1
    rw [hs] at hs₀
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs₀
    refine ⟨⟨x i, hsm _ (hxy i).1, fun h => hi ?_⟩, ⟨y i, hsm _ (hxy i).2, fun h => hi ?_⟩⟩
    · rw [h, inner_zero_left]
    · rw [h, map_zero, inner_zero_right]
  have hex : ∀ ν, ∃ (s : ℂ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
      (ν = 0 → F = fun g => ((dg 0 / ‖s₀‖ : ℝ) : ℂ) • f g) ∧
      (n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) → IsCoef (R ν) (l ν) (l' ν) F s ∧ ‖s‖ = dg ν) ∧
      (¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → F = 0) := by
    intro ν
    by_cases hν : ν = 0
    · subst hν
      refine ⟨((dg 0 / ‖s₀‖ : ℝ) : ℂ) * s₀, _, fun _ => rfl, fun _ _ _ => ⟨?_, ?_⟩, fun hn => ?_⟩
      · exact (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R 0) Wp Wq (l 0) (l' 0) (hDS 0 h0)).2.1 f s₀ _ hf
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos hdg0 hsn).le]
        field_simp
      · exact absurd ⟨h0, hnz⟩ hn
    · by_cases hc : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
      · obtain ⟨h1, h2, h3⟩ := hc
        have e1 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wp _ _ (l ν) (hDS ν h1) (hL ν h1).1.1 h2
        have e2 := GlobalTheory.bessel_nonzero_on_translates hH _ _ _ _ (R ν) Wq _ _ (l' ν) (hDS ν h1) (hR ν h1).1.1 h3
        obtain ⟨F, hF⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hK _ _ _ _ (R ν) Wp Wq (l ν) (l' ν)
          (hDS ν h1)).2.2 e1 e2 (dg ν : ℂ)
        refine ⟨_, F, fun h => absurd h hν, fun _ _ _ => ⟨hF, ?_⟩, fun hn => absurd ⟨h1, h2, h3⟩ hn⟩
        rw [Complex.norm_real, Real.norm_of_nonneg (hL ν h1).2.1.le]
      · exact ⟨0, 0, fun h => absurd h hν, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hc, fun _ => rfl⟩
  choose s J h1 h2 h3 using hex
  exact ⟨s, J, dg 0 / ‖s₀‖, div_pos hdg0 hsn, h1 0 rfl, hnz, h2, h3⟩

end GlobalTheory
