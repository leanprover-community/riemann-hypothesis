module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsGlueDataPre
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

def LastUnit : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueDataPre h U 𝔭 a π w c τ →
      ∀ j : Fin (finrank K (orthK h U)), (j : ℕ) + 1 = finrank K (orthK h U) →
      ∃ l : K, l ≠ 0 ∧ InP 𝔭 0 (algebraMap F K (c j) * (l * star l)) ∧
        InP 𝔭 0 (algebraMap F K (c j) * (l * star l))⁻¹

theorem lastRescale_of (hL : LastUnit) : LastRescale := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg
  have hm : 0 < finrank K (orthK h U) := lt_of_le_of_lt (Nat.zero_le _) hc
  set j₀ : Fin (finrank K (orthK h U)) := ⟨finrank K (orthK h U) - 1, by omega⟩ with hj₀
  obtain ⟨l, hl0, hl1, hl2⟩ :=
    hL K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg j₀ (by simp [j₀]; omega)
  obtain ⟨hwW, hwo, hwn, hτ, hu, hcong, hτl, hunit⟩ := hg
  obtain ⟨μ, hμ⟩ := (hF (l * star l)).1 (by rw [star_mul', star_star, mul_comm])
  have hμ0 : μ ≠ 0 := by
    intro e; rw [e, map_zero] at hμ
    exact mul_ne_zero hl0 (star_ne_zero.2 hl0) hμ.symm
  let w' := Function.update w j₀ (l • w j₀)
  let c' := Function.update c j₀ (μ * c j₀)
  have hw'₀ : w' j₀ = l • w j₀ := Function.update_self _ _ _
  have hw'n : ∀ j, j ≠ j₀ → w' j = w j := fun j hj => Function.update_of_ne hj _ _
  have hc'₀ : c' j₀ = μ * c j₀ := Function.update_self _ _ _
  have hc'n : ∀ j, j ≠ j₀ → c' j = c j := fun j hj => Function.update_of_ne hj _ _
  have hτ₀ : ∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j₀ := by
    intro i hi e
    have := hτl i hi
    rw [e] at this
    simp [j₀] at this
    omega
  refine ⟨w', c', ⟨?_, ?_, ?_, hτ, hu, ?_, ?_⟩⟩
  · intro j
    by_cases hj : j = j₀
    · rw [hj, hw'₀]; exact Submodule.smul_mem _ _ (hwW j₀)
    · rw [hw'n j hj]; exact hwW j
  · intro j k hjk
    by_cases hj : j = j₀
    · have hk : k ≠ j₀ := fun e => hjk (hj.trans e.symm)
      rw [hj, hw'₀, hw'n k hk, form_smul_left, hwo _ _ (hj ▸ hjk), mul_zero]
    · by_cases hk : k = j₀
      · rw [hk, hw'₀, hw'n j hj, form_smul_right, hwo _ _ (hk ▸ hjk), mul_zero]
      · rw [hw'n j hj, hw'n k hk]; exact hwo j k hjk
  · intro j
    by_cases hj : j = j₀
    · rw [hj, hw'₀, hc'₀, form_smul_smul, (hwn j₀).1, map_mul, hμ]
      refine ⟨by ring, mul_ne_zero hμ0 (hwn j₀).2⟩
    · rw [hw'n j hj, hc'n j hj]; exact hwn j
  · intro i hi
    rw [hc'n _ (hτ₀ i hi)]; exact hcong i hi
  · intro j hnp
    by_cases hj : j = j₀
    · rw [hj, hc'₀]
      refine ⟨?_, ?_⟩
      · rw [map_mul, hμ, mul_comm]; exact hl1
      · rw [map_inv₀, map_mul, hμ, mul_comm]; exact hl2
    · rw [hc'n j hj]
      refine hunit j ?_ hnp
      have h1 := j.isLt
      have h2 : (j : ℕ) ≠ finrank K (orthK h U) - 1 := fun e => hj (Fin.ext e)
      omega

end Formalism.L2.SG.Pf.GluingBases
