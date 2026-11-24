module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DiscriminantEigenProjector
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.EigExt

theorem mem_eigSp_iff' {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    (ρ : O →+* Module.End R E) (σ : O →+* R) (v : E) :
    v ∈ eigSp ρ σ ↔ ∀ a, ρ a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem eigSp_ext :
    ∀ (F : Type) [Field F] [NumberField F] (Ω Ω' : Type) [Field Ω] [Field Ω'] [CharZero Ω] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (ρ : 𝓞 F →+* Module.End Ω V) (ρ' : 𝓞 F →+* Module.End Ω' V') (σ : 𝓞 F →+* Ω), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → (∀ a e, ρ' a (j e) = j (ρ a e)) → eigSp ρ' (i.comp σ) = Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) := by
  intro F _ _ Ω Ω' _ _ _ i V V' _ _ _ _ j ρ ρ' σ hj hspan hcomp
  obtain ⟨n, a, c, hsum, hcas⟩ := GlobalTheory.CompanionTheory.Ar.ScaledCasimir.exists_scaledCasimir F

  let P' : V' →ₗ[Ω'] V' := ∑ m, i (σ (c m)) • ρ' (a m)
  have hP'apply : ∀ w, P' w = ∑ m, i (σ (c m)) • ρ' (a m) w := fun w => by
    simp [P', LinearMap.sum_apply]
  have hscal : ∑ m, i (σ (c m)) * i (σ (a m)) = ((NumberField.discr F : ℤ) : Ω') := by

    rw [← map_intCast (i.comp σ), ← hsum, map_sum]
    simp [map_mul]
  have hP'eig : ∀ w ∈ eigSp ρ' (i.comp σ), P' w = ((NumberField.discr F : ℤ) : Ω') • w := by
    intro w hw
    have hw' := (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ' (i.comp σ) w).mp hw
    calc P' w = ∑ m, i (σ (c m)) • ρ' (a m) w := hP'apply w
      _ = ∑ m, (i (σ (c m)) * i (σ (a m))) • w :=
          Finset.sum_congr rfl fun m _ => by rw [hw', RingHom.comp_apply, smul_smul]
      _ = _ := by rw [← Finset.sum_smul, hscal]
  have hP'j : ∀ e, P' (j e) = j (∑ m, σ (c m) • ρ (a m) e) := by
    intro e

    rw [hP'apply, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcomp, hj.1]
  have hPe : ∀ e, ∑ m, σ (c m) • ρ (a m) e ∈ eigSp ρ σ := fun e =>
    (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ σ _).mpr fun b => hcas Ω V ρ σ b e
  apply le_antisymm
  · intro w hw
    have hle : Submodule.span Ω' (Set.range j) ≤
        (Submodule.span Ω' (j '' (eigSp ρ σ : Set V))).comap P' := by
      rw [Submodule.span_le]
      rintro _ ⟨e, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, hP'j]
      exact Submodule.subset_span ⟨_, hPe e, rfl⟩
    have hmem : P' w ∈ Submodule.span Ω' (j '' (eigSp ρ σ : Set V)) :=
      hle (by rw [hspan]; exact Submodule.mem_top)
    rw [hP'eig w hw] at hmem
    have hd : ((NumberField.discr F : ℤ) : Ω') ≠ 0 := by
      rw [← map_intCast i]
      exact (map_ne_zero i).mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero F))
    have h2 := Submodule.smul_mem _ ((NumberField.discr F : ℤ) : Ω')⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at h2
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ σ v).mp hv
    refine (GlobalTheory.CompanionTheory.Ar.EigExt.mem_eigSp_iff' ρ' (i.comp σ) (j v)).mpr fun b => ?_
    rw [hcomp, hv' b, hj.1, RingHom.comp_apply]

end GlobalTheory.CompanionTheory.Ar.EigExt
