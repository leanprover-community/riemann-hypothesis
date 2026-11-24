module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLAtPrimeOfCongruentOneModPow
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

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.VolBridge.StabRead

variable {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k]
  {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}

theorem mem_stdAt_iff_int (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (v : Sp E M) :
    v ∈ stdAt E M P ↔ ∀ i, ι (v i) ∈ 𝒪[k] := by
  rw [GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.mem_stdAt]
  exact forall_congr' fun i => (hι _).symm

theorem single_mem_stdAt (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (m : Fin M) :
    (Pi.single m 1 : Sp E M) ∈ stdAt E M P := by
  rw [mem_stdAt_iff_int hι]
  intro i
  rw [Pi.single_apply]
  split_ifs
  · rw [map_one]; exact Subring.one_mem _
  · rw [map_zero]; exact Subring.zero_mem _

theorem map_mem_stdAt (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (y : Sp E M ≃ₗ[E] Sp E M)
    (hy : ∀ i m, ι (y (Pi.single m 1) i) ∈ 𝒪[k]) {v : Sp E M} (hv : v ∈ stdAt E M P) : y v ∈ stdAt E M P := by
  rw [mem_stdAt_iff_int hι] at hv ⊢
  intro i
  have e : y v = LinearMap.toMatrix' (y : Sp E M →ₗ[E] Sp E M) *ᵥ v := (LinearMap.toMatrix'_mulVec _ v).symm
  rw [e]

  simp only [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply, map_sum, map_mul]
  exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hy i m) (hv m)

end GlobalTheory.VolBridge.StabRead


open GlobalTheory.VolBridge.StabRead in
theorem GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k)
    (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M)
    (x : Sp E M ≃ₗ[E] Sp E M) : x ∈ stabL E M (stdAt E M P) ↔ locHom ι e x ∈ KO k A := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ stabL E M (stdAt E M P) := inv_mem hx
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · change ι (x (Pi.single (e b) 1) (e a)) ∈ 𝒪[k]
      exact (mem_stdAt_iff_int hι _).1 ((hx _).2 (single_mem_stdAt hι _)) _
    · change ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single (e b) 1) (e a)) ∈ 𝒪[k]
      exact (mem_stdAt_iff_int hι _).1 ((hx' _).2 (single_mem_stdAt hι _)) _
  · rintro ⟨h1, h2⟩
    have i1 : ∀ i m, ι (x (Pi.single m 1) i) ∈ 𝒪[k] := fun i m => by
      have h := h1 (e.symm i) (e.symm m)
      change ι (x (Pi.single (e (e.symm m)) 1) (e (e.symm i))) ∈ 𝒪[k] at h
      simpa only [Equiv.apply_symm_apply] using h
    have i2 : ∀ i m, ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single m 1) i) ∈ 𝒪[k] := fun i m => by
      have h := h2 (e.symm i) (e.symm m)
      change ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single (e (e.symm m)) 1) (e (e.symm i))) ∈ 𝒪[k] at h
      simpa only [Equiv.apply_symm_apply] using h
    intro v
    constructor
    · intro hv
      have h := map_mem_stdAt hι _ i2 hv
      have ev : (x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (x v) = v := x.symm_apply_apply v
      rwa [ev] at h
    · exact map_mem_stdAt hι x i1
