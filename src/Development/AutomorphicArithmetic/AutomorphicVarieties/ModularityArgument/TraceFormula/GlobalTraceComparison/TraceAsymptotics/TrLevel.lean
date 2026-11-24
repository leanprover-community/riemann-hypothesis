module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevOpMemFixed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open scoped Classical

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.trLevel :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel := by
  intro G _ _ _ K _ hK V _ _ ρ f K₁ K₂ h₂ hle h₁K hf hfd
  have h₁ : IsOpen (K₁ : Set G) := Subgroup.isOpen_mono hle h₂
  haveI : Finite (K₁ ⧸ K₂.subgroupOf K₁) := GlobalTheory.TwTrLevel.finite_quot K K₁ K₂ hK h₁ h₂ h₁K
  have hf₂ : IsHecke K₂ f := ⟨hf.1, fun k hk x => hf.2 k (hle hk) x⟩
  have stable : ∀ (H : Subgroup G), IsOpen (H : Set G) → IsHecke H f →
      ∀ v ∈ fixed ρ H, levOp ρ K H f LinearMap.id v ∈ fixed ρ H := fun H hH hfH v hv =>
    GlobalTheory.TwTrLevel.levOp_mem_fixed ρ (MonoidHom.id G) (fun _ => rfl) LinearMap.id (fun _ => rfl) K H hH
      (fun _ hk => hk) f hfH v hv
  have c₁ := stable K₁ h₁ hf
  have c₂ := stable K₂ h₂ hf₂
  have hW : fixed ρ K₁ ≤ fixed ρ K₂ := fun v hv => by
    rw [GlobalTheory.TwTrLevel.mem_fixed_iff] at hv ⊢
    exact fun k hk => hv k (hle hk)
  haveI : FiniteDimensional ℂ (fixed ρ K₂) := hfd
  haveI : FiniteDimensional ℂ (fixed ρ K₁) := Submodule.finiteDimensional_of_le hW
  let incl : fixed ρ K₁ →ₗ[ℂ] fixed ρ K₂ := Submodule.inclusion hW
  let T : fixed ρ K₂ →ₗ[ℂ] fixed ρ K₁ :=
    ((levOp ρ K K₁ f LinearMap.id).restrict c₁) ∘ₗ
      ((GlobalTheory.TwTrLevel.avgOp ρ K₁ K₂).restrict fun u hu => GlobalTheory.TwTrLevel.avgOp_mem ρ K₁ K₂ u hu)
  have e₂ : (levOp ρ K K₂ f LinearMap.id).restrict c₂ = incl ∘ₗ T := by
    ext v
    simp only [LinearMap.restrict_coe_apply, LinearMap.coe_comp, Function.comp_apply, incl, T,
      Submodule.coe_inclusion]
    exact GlobalTheory.TwTrLevel.levOp_le ρ K K₁ K₂ hle h₁K h₁ h₂ f hf _ v.2
  have e₁ : (levOp ρ K K₁ f LinearMap.id).restrict c₁ = T ∘ₗ incl := by
    ext w
    simp only [LinearMap.restrict_coe_apply, LinearMap.coe_comp, Function.comp_apply, incl, T,
      Submodule.coe_inclusion]
    rw [GlobalTheory.TwTrLevel.avgOp_fix ρ K₁ K₂ _ w.2]
  unfold twTr
  rw [dite_eq_left c₂, dite_eq_left c₁, e₂, e₁, LinearMap.trace_comp_comm']
