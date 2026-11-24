module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariantStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem betaD_dvd_of_res : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ y : Per.BdRp l, (∀ k : ℕ, ∃ s ∈ Sg ϖ, betaD ϖ ∣ y - ((l : ℕ) : Per.BdRp l) ^ k * s) → betaD ϖ ∣ y := by
  intro l _ ϖ hk hF y hy
  obtain ⟨-, hker, hA, hD, -⟩ := GlobalTheory.MemLoc.thetaP_facts l
  have hb0 : Per.θP l (beta ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker, hk]; exact Ideal.mem_span_singleton_self _
  have hb : Per.θD l (betaD ϖ) = 0 := by rw [betaD, hD, hb0]
  have hS : ∀ a ∈ Sa ϖ, Per.θP l a ∈ 𝓞_ℂ_[l] := by
    intro a ha
    change a ∈ Algebra.adjoin _ _ at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => rw [Set.mem_singleton_iff.1 hx, hb0]; exact zero_mem _
    | algebraMap r => rw [hA]; exact (Per.θ l r).2
    | add x z _ _ hx hz => rw [map_add (Per.θP l)]; exact add_mem hx hz
    | mul x z _ _ hx hz => rw [map_mul]; exact mul_mem hx hz
  have hs : ∀ s ∈ Sg ϖ, ‖Per.θD l s‖ ≤ 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hD]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (hS a ha)
  have h0 : Per.θD l y = 0 := by
    have hle : ∀ k : ℕ, ‖Per.θD l y‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ ^ k := by
      intro k
      obtain ⟨s, hsS, c, hc⟩ := hy k
      have h1 := congrArg (Per.θD l) hc
      rw [map_sub, map_mul, map_mul, hb, zero_mul, sub_eq_zero, map_pow, map_natCast] at h1
      rw [h1, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hs s hsS)
    exact norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (GlobalTheory.RingBasics.norm_p_lt (p := l))) hle)
  have hmem : y ∈ Per.FilP l 1 := ((GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.1 y).1 h0
  rw [hF 1, pow_one] at hmem
  exact Ideal.mem_span_singleton.1 hmem

end GlobalTheory.Pst.StLat
