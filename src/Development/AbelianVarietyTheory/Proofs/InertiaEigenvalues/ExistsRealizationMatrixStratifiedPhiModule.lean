module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitAndAinfSaturatedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.RealMatrix

section Alg

variable {R R' : Type} [CommRing R] [CommRing R'] {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem map_smul_hom (f : R →+* R') (c : R) (M : Matrix n n R) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobenius_matrix_equation_inverse_scaling (F : R →+* R) (e t v : R) (hv : v * t = 1) (ht : F t = e * t) (a N : ℕ) (Y A : Matrix n n R)
    (h : e ^ a • Y.map F = Y * A) : e ^ (a + N) • (v ^ N • Y).map F = (v ^ N • Y) * A := by
  have h1 : F v * (e * t) = 1 := by rw [← ht, ← map_mul, hv, map_one]
  have h2 : e * F v = v := by linear_combination v * h1 - (e * F v) * hv
  have h3 : e ^ (a + N) * F v ^ N = v ^ N * e ^ a := by
    rw [pow_add, mul_assoc, ← mul_pow, h2, mul_comm]
  rw [map_smul_hom, map_pow, smul_smul, h3, ← smul_smul, h, Matrix.smul_mul]

theorem galois_matrix_equation_inverse_scaling (G : R →+* R) (t v : R) (hv : v * t = 1) (N : ℕ) (P Y ε : Matrix n n R)
    (h : t ^ N • (P * Y.map G) = G t ^ N • (Y * ε)) : P * (v ^ N • Y).map G = (v ^ N • Y) * ε := by
  have h1 : G v * G t = 1 := by rw [← map_mul, hv, map_one]
  have h2 := congrArg (fun M => (v ^ N * G v ^ N) • M) h
  have h3 : v ^ N * G v ^ N * t ^ N = G v ^ N := by
    rw [mul_right_comm, ← mul_pow, hv, one_pow, one_mul]
  have h4 : v ^ N * G v ^ N * G t ^ N = v ^ N := by
    rw [mul_assoc, ← mul_pow, h1, one_pow, mul_one]
  simp only [smul_smul, h3, h4] at h2
  rw [map_smul_hom, map_pow, Matrix.mul_smul, h2, Matrix.smul_mul]

theorem descend (f : R →+* R') (hf : Function.Injective f) (x y : R) (N : ℕ) (M Y ε : Matrix n n R)
    (h : f x ^ N • M.map f = f y ^ N • (Y.map f * ε.map f)) : x ^ N • M = y ^ N • (Y * ε) := by
  apply Matrix.map_injective hf
  simp only []
  rw [map_smul_hom, map_smul_hom, map_pow, map_pow, Matrix.map_mul, h]

theorem push (f : R →+* R') (x y : R) (N : ℕ) (P Q Y ε : Matrix n n R) (h : x ^ N • (P * Q) = y ^ N • (Y * ε)) :
    f x ^ N • (P.map f * Q.map f) = f y ^ N • (Y.map f * ε.map f) := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_pow, ← map_pow, ← map_smul_hom, ← map_smul_hom, h]

end Alg

theorem exists_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ S : Strat bk d, S.a = ht.a + s.N → S.A = ht.A → (∀ g : ↥(GK K), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ((S.ε bk.ι ((ainfHom K g).comp bk.ι)).map bk.iA)) → ∃ T : Matrix (Fin d) (Fin d) (WCb l), MReal S ρ T := by
  intro l _ K bk d ρ τ s ht hτ S ha hA hrel
  obtain ⟨u, hu⟩ := (GlobalTheory.T.breuilKisin_period_isUnit_and_ainf_saturated l K bk τ hτ).1
  have hv : (↑u⁻¹ : WCb l) * inclW l τ = 1 := by rw [← hu, Units.inv_mul]
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  refine ⟨(↑u⁻¹ : WCb l) ^ s.N • ht.Y.map (inclW l), ?_, ?_, ?_⟩
  · rw [Algebra.smul_def]
    exact (((Units.isUnit _).pow _).map _).mul ht.unit
  · rw [ha, hA]
    refine frobenius_matrix_equation_inverse_scaling (frobW l : WCb l →+* WCb l) (bk.evW bk.E) (inclW l τ) _ hv ?_ _ _ _ _ ?_
    · change frobW l (inclW l τ) = inclW l (bk.ev bk.E) * inclW l τ
      rw [frobW_inclW, hτ.1, map_mul]
    · have h := congrArg (fun M => M.map (inclW l)) ht.φ
      try beta_reduce at h
      rw [map_smul_hom, map_pow, Matrix.map_mul] at h
      refine Eq.trans ?_ h
      congr 1
      ext1 i j
      exact frobW_inclW _
  · intro g
    have h0 := descend bk.iA hinj _ _ _ _ _ _ (GlobalTheory.T.rel_galois_comparison_matrix l K bk d ρ τ s ht hτ g _ (hrel g))
    have h := push (inclW l) _ _ _ _ _ _ _ h0
    rw [← galW_inclW] at h
    refine galois_matrix_equation_inverse_scaling (galW l (g : GQ l) : WCb l →+* WCb l) (inclW l τ) _ hv _ _ _ _ ?_
    refine Eq.trans ?_ h
    congr 2
    · ext1 i j
      exact ((inclWA l).commutes _).symm
    · ext1 i j
      exact galW_inclW _ _

end GlobalTheory.BSP.RealMatrix
