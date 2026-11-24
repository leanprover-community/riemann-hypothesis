module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.DualWeyl MvPolynomial NumberField IsDedekindDomain
open Formalism.L2.DIV (colLat IsBasisAt dualFr)
open Formalism.HermitianLatticesTheory (localization₂)
open scoped Matrix

namespace GlobalTheory.DualWeylDual

variable {K : Type} [Field K] {N : ℕ}

theorem exists_smul_mem_of_le_locP (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : M ≤ localization₂ w.asIdeal M') : ∃ t ∈ w.asIdeal.primeCompl, ∀ x ∈ M, t • x ∈ M' := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have h1 : ∀ y : s, ∃ a ∈ w.asIdeal.primeCompl, a • (y : Fin N → K) ∈ M' := fun y =>
    h (Submodule.subset_span y.2)
  choose a ha0 ha using h1
  refine ⟨∏ y, a y, Submonoid.prod_mem _ fun y _ => ha0 y, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨y, hy⟩ : s)), mul_smul]
    exact M'.smul_mem _ (ha ⟨y, hy⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact M'.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact M'.smul_mem _ hy

theorem localization_dualFr_le (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : localization₂ w.asIdeal M ≤ localization₂ w.asIdeal M') :
    localization₂ w.asIdeal (dualFr M') ≤ localization₂ w.asIdeal (dualFr M) := by
  obtain ⟨t, ht, htM⟩ := exists_smul_mem_of_le_locP w hM
    (fun x hx => h ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩)
  rintro φ ⟨s, hs, hφ⟩
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, fun x hx => ?_⟩
  have h1 : (s • φ) ⬝ᵥ (t • x) ∈ (1 : Submodule (𝓞 K) K) := hφ _ (htM x hx)
  rwa [dotProduct_smul, ← smul_dotProduct, smul_smul] at h1

theorem dualFr_colLat (B : GL (Fin N) K) : dualFr (colLat B) = colLat (Formalism.BasicNotions.inside₂ K N B) := by
  apply SetLike.ext
  intro φ
  rw [mem_colLat_iff]
  constructor
  · intro h
    have h1 : ∀ j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ fun a => (B : Matrix (Fin N) (Fin N) K) a j := fun j =>
      Submodule.mem_one.mp (h _ (Submodule.subset_span ⟨j, rfl⟩))
    choose c hc using h1
    refine ⟨c, ?_⟩
    have h2 : (fun j => (c j : K)) = (B : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ φ := by
      funext j
      rw [Matrix.mulVec_transpose]
      exact hc j
    rw [h2, Matrix.mulVec_mulVec]
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ * _) *ᵥ φ = φ
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mulVec]
  · rintro ⟨c, rfl⟩ x hx
    obtain ⟨d, rfl⟩ := (mem_colLat_iff _ _).mp hx
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ _) ⬝ᵥ _ ∈ _
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    refine Submodule.mem_one.mpr ⟨c ⬝ᵥ d, ?_⟩
    simp [dotProduct]

theorem isBasisAt_dualFr (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) (Fin N → K)} (hL : L.FG)
    {B : GL (Fin N) K} (hB : IsBasisAt w L B) : IsBasisAt w (dualFr L) (Formalism.BasicNotions.inside₂ K N B) := by
  unfold IsBasisAt at hB ⊢
  rw [← dualFr_colLat]
  exact le_antisymm (localization_dualFr_le w (Submodule.fg_span (Set.finite_range _)) hB.ge) (localization_dualFr_le w hL hB.le)

end GlobalTheory.DualWeylDual
