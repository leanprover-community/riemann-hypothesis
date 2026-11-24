module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.SymbolEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IotaEx
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
import Mathlib.Order.CompletePartialOrder
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

namespace UpperTheory.V.Z.Sym.Glob

open Matrix Loc

private theorem base_bot {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (ι : Γ →* G) (U : Subgroup G)
    (W : Representation ℂ Γ V) : ∃ B : Base Γ G V, B.ι = ι ∧ B.U = U ∧ B.ω = 1 ∧ B.Γ₀ = ⊥ ∧ B.W = W := by
  refine ⟨⟨ι, U, 1, W, ⊥, bot_le, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
  · intro z hz
    rw [Subgroup.mem_bot.1 hz, map_one]
    exact one_mem _
  · intro z hz
    rw [Subgroup.mem_bot.1 hz, map_one]
    exact one_mem _
  · intro z hz v
    obtain rfl := Subgroup.mem_bot.1 hz
    simp

private theorem base_sub {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (ι : Γ →* G) (S : Subgroup Γ)
    (T U : Subgroup G) (h : ∀ γ ∈ S, ι γ ∈ T) (x : G) (W : Representation ℂ S V) :
    ∃ B : Base S T V, (∀ γ : S, (B.ι γ : G) = ι γ) ∧ (∀ g : T, g ∈ B.U ↔ x⁻¹ * g * x ∈ U) ∧ B.ω = 1 ∧ B.Γ₀ = ⊥ ∧ B.W = W := by
  obtain ⟨B, h1, h2, h3⟩ := base_bot ((ι.comp S.subtype).codRestrict T fun γ => h γ γ.2)
    ((U.comap (MulAut.conj x⁻¹).toMonoidHom).subgroupOf T) W
  refine ⟨B, fun γ => by rw [h1]; rfl, fun g => ?_, h3⟩
  rw [h2, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  simp

private theorem mem_SU {K : Type} [Field K] {Δ : K} (g : DX Δ) : g ∈ SU Δ ↔ (mt g).det = 1 := by
  rw [SU, MonoidHom.mem_ker, ← Units.val_eq_one]
  rfl

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob in
theorem UpperTheory.V.Z.Sym.Glob.baseS :
    UpperTheory.V.Z.Sym.Glob.BaseS := by
  intro F _ _ Δ D _ V _ _ W ch htr x
  obtain ⟨-, ⟨ι, hι⟩, -⟩ := iotaEx F Δ
  have hmem : ∀ γ ∈ SU Δ, ι γ ∈ SA Δ := by
    intro γ hγ
    refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_comap.2 ((mem_SU _).2 ?_)
    have h1 : (mt ((ι γ).1 v)).det = 1 := by
      rw [hι γ v, ← RingHom.mapMatrix_apply, ← RingHom.map_det, (mem_SU γ).1 hγ, map_one]
    exact h1
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := base_sub ι (SU Δ) (SA Δ) D.U2 hmem x W
  refine ⟨B, ⟨fun γ v => ?_, h2, h3, h4, fun γ τ h => ?_⟩, h5⟩
  · rw [h1]
    exact hι _ v
  · rw [h5]
    exact htr γ τ h
