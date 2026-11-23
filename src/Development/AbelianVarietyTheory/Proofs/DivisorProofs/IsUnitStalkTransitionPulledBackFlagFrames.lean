module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsCompEqOfFunctionFieldMapsAgreeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem GlobalTheory.FlagPush.Dbl.transition_par_stalk : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ z : W.Z, ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), Par 0 (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) := by
  intro F _ X Y ι _ m E E' φ f hR W hW z A₁ hA₁ A₂ hA₂
  have hbase := GlobalTheory.T.maps_comp_eq_of_functionField_maps_agree F X Y φ f hR.hom W hW
  have hf : f (W.p₁ z) = f (W.p₂ z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hbase]
  obtain ⟨A, hA⟩ := E.nonempty (f (W.p₁ z))
  have hA' : A ∈ E.S (f (W.p₂ z)) := hf ▸ hA
  have h₁ := hR.sub _ A₁ hA₁ A hA
  have h₂ := hR.sub _ A₂ hA₂ A hA'
  have reg : ∀ (p : W.Z ⟶ Y.X) [IsDominant p], ∀ x ∈ ((ratOf Y).O (p z)).toSubring,
      functionFieldMap p x ∈ (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range := by
    intro p _ x hx
    obtain ⟨a, rfl⟩ := mem_O_ratOf.1 hx
    exact ⟨_, (functionFieldMap_algebraMap p z a).symm⟩
  have k₁ := h₁.map W.α₁ (reg W.p₁)
  have k₂ := h₂.map W.α₂ (reg W.p₂)
  set B : Mat m Y.Fn := A.map φ with hBdef
  have hB : ∀ τ, (B τ).det ≠ 0 := fun τ => by
    intro h
    exact Fr.det_ne hA τ ((map_eq_zero (φ : X.Fn →+* Y.Fn)).1 (((φ : X.Fn →+* Y.Fn).map_det (A τ)).trans h))
  have hB₂ : ∀ τ, (B.map W.α₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hB τ)
  have e12 : B.map W.α₁ = B.map W.α₂ := by
    funext τ; ext i j; exact hW (A τ i j)
  have d₁ : A₁ = A₁ * B⁻¹ * B := by rw [mul_assoc, Mat.inv_mul hB, mul_one]
  have d₂ : A₂ = A₂ * B⁻¹ * B := by rw [mul_assoc, Mat.inv_mul hB, mul_one]
  have key : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ = (A₁ * B⁻¹).map W.α₁ * ((A₂ * B⁻¹).map W.α₂)⁻¹ := by
    conv_lhs => rw [d₁, d₂]
    rw [Mat.map_mul _ _ W.α₁, Mat.map_mul _ _ W.α₂, e12, Mat.mul_inv_rev, mul_assoc, ← mul_assoc (B.map W.α₂),
      Mat.mul_inv hB₂, one_mul]
  rw [key]
  exact k₁.mul k₂.inv
