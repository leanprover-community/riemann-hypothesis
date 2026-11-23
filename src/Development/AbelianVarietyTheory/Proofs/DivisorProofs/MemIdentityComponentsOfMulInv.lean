module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdentityComponentsSmoothGroupSchemeMulMemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemConnectedComponentInFibreStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem identityComponent_shear_mul {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    lift (fst G G ≫ ι[G]) μ[G] ≫ μ[G] = snd G G := by
  have h1 : lift (fst G G ≫ ι[G]) μ[G] ≫ μ[G] = (fst G G)⁻¹ * (fst G G * snd G G) := by
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Hom.inv_def]
  rw [h1, inv_mul_cancel_left]

theorem mem_identityComponents_of_mul_inv :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (∀ z ∈ U, G.hom z = G.hom y → z ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G _ hs U y hU hy
  obtain ⟨w, hf, hm, rfl⟩ := hy
  have hbf : G.hom ((fst G G).left w) = G.hom ((snd G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w, Over.w]
  have hbm : G.hom ((μ[G]).left w) = G.hom ((snd G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w, Over.w]
  have zf := hU _ hf hbf
  have zm := hU _ hm hbm
  have zi := GlobalTheory.T.inv_mem_identity_component_fibre S G _ zf
  set φ : G ⊗ G ⟶ G ⊗ G := lift (fst G G ≫ ι[G]) μ[G] with hφ
  have e1 : (fst G G).left (φ.left w) = (ι[G]).left ((fst G G).left w) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, hφ, lift_fst]
  have e2 : (snd G G).left (φ.left w) = (μ[G]).left w := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφ, lift_snd]
  have key := GlobalTheory.T.identityComponents_smooth_groupScheme_mul_mem S G hs (φ.left w) (e1 ▸ zi) (e2 ▸ zm)
  have e3 : (μ[G]).left (φ.left w) = (snd G G).left w := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφ, identityComponent_shear_mul]
  rwa [e3] at key

end GlobalTheory
