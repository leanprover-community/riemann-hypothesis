module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_phiSt_invariant_nondegenerate_linearForm :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ lam : Bst P →ₗ[ℚ_[l]] ℚ_[l], (∀ c : ↥(K0 K), lam (phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) = lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) ∧ ∀ c : ↥(K0 K), (∀ c' : ↥(K0 K), lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c') * Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = 0) → c = 0 := by
  intro l _ P K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _

  let ι : ↥(K0 K) →ₗ[ℚ_[l]] Bst P :=
    ((Polynomial.monomial 0 : P.R.B →ₗ[P.R.B] Polynomial P.R.B).restrictScalars ℚ_[l]).comp
      (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap
  have hι : ∀ c, ι c = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := fun c => by
    simp [ι, Polynomial.monomial_zero_left]
  have hinj : Function.Injective ι := by
    intro a b hab
    rw [hι, hι] at hab
    exact (algebraMap ↥(K0 K) P.R.B).injective (Polynomial.C_injective hab)

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hinj)
  have hgι : ∀ c, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  refine ⟨(Algebra.trace ℚ_[l] ↥(K0 K)).comp g, ?_, ?_⟩
  ·
    intro c
    have hφ : phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = ι ((P.PD K).σ c) := by
      have hC : ∀ b : P.R.B, phiSt P (Polynomial.C b) = Polynomial.C (P.φB b) := fun b => by
        simp [phiSt, stHom]
      rw [hC, ← P.PD_φ K, (P.PD K).φ_K₀, hι]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hφ, ← hι, hgι, hgι]
    exact Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij) c
  ·
    intro c h
    by_contra hc
    have h1 := h c⁻¹
    rw [← map_mul, ← map_mul, ← hι, LinearMap.comp_apply, hgι, inv_mul_cancel₀ hc] at h1
    have h2 : Algebra.trace ℚ_[l] ↥(K0 K) 1 = (Module.finrank ℚ_[l] ↥(K0 K) : ℚ_[l]) := by
      rw [← map_one (algebraMap ℚ_[l] ↥(K0 K)), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') h1

end GlobalTheory.PMon
