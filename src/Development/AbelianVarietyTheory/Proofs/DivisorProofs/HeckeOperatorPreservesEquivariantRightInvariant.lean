module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

def leftEqv {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G)
    (ρ : Representation ℂ H V) : Submodule ℂ (G → V) where
  carrier := {φ | ∀ h x, φ (ι h * x) = ρ h (φ x)}
  add_mem' := by
    intro a b ha hb h x
    simp only [Pi.add_apply, ha h x, hb h x, map_add (f := _)]
  zero_mem' := fun _ _ => by simp
  smul_mem' := by
    intro c a ha h x
    simp only [Pi.smul_apply, ha h x, map_smul]

theorem eqvM_eq_inf {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G)
    (ρ : Representation ℂ H V) (K : Subgroup G) :
    eqvM ι ρ K = leftEqv ι ρ ⊓ fixed (rightReg ℂ G V) K := by
  ext φ
  simp only [Submodule.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k => ?_⟩
    funext x
    simpa [rightReg, LinearMap.funLeft] using h2 k k.2 x
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk x => ?_⟩
    have := congrFun (h2 ⟨k, hk⟩) x
    simpa [rightReg, LinearMap.funLeft] using this

theorem levOp_rightReg_mem_eqvM : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G) (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) → ∀ φ ∈ eqvM ι ρ K', levOp (rightReg ℂ G V) K K' F LinearMap.id φ ∈ eqvM ι ρ K' := by
  intro G H V _ _ _ _ ι ρ K K' F hF φ hφ
  rw [eqvM_eq_inf] at hφ ⊢
  refine levOp_id_mem_inf_fixed (rightReg ℂ G V) K K' F hF (leftEqv ι ρ) ?_ φ hφ
  intro g v hv h x
  simp only [rightReg, LinearMap.funLeft, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply]
  rw [mul_assoc]
  exact hv h (x * g)

end GlobalTheory.BCT.TraceBlocks
