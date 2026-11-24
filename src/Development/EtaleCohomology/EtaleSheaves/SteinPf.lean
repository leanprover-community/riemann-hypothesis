module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SteinPf
open LateralTheory.E.t_E2Cut

def RelNorm : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], AICSch Z →
  ∃ (T : Scheme.{0}) (c : Z ⟶ T) (k : T ⟶ S), IsIntegral T ∧ IsDominant c ∧ IsIntegralHom k ∧ c ≫ k = g ∧
    ∀ V : T.Opens, IsAffineOpen V → (V : Set T).Nonempty →
      ((c ⁻¹ᵁ V : Set Z).Nonempty ∧ Function.Injective (c.app V) ∧
        ∀ b : Γ(Z, c ⁻¹ᵁ V), (c.app V).hom.IsIntegralElem b → ∃ a, c.app V a = b)

def AICOpen : Prop := ∀ {Z : Scheme.{0}}, AICSch Z → ∀ W : Z.Opens, (W : Set Z).Nonempty → AIC Γ(Z, W)

theorem aic_of_int {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hB : AIC B) (hi : Function.Injective φ)
    (hc : ∀ b : B, φ.IsIntegralElem b → ∃ a, φ a = b) (hn : Nontrivial B) : AIC A := by
  intro p hm hd
  obtain ⟨b, hb⟩ := hB (p.map φ) (hm.map φ) (by rw [hm.natDegree_map]; exact hd)
  obtain ⟨a, rfl⟩ := hc b ⟨p, hm, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  refine ⟨a, hi ?_⟩
  rw [map_zero, ← Polynomial.eval_map_apply]; exact hb

theorem Stein_of (hR : RelNorm) (hA : AICOpen) : Stein := by
  intro Z S g _ _ hZ
  obtain ⟨T, c, k, hT, hc, hk, hck, hV⟩ := hR g hZ
  refine ⟨T, c, k, ⟨hT, fun V hV' hne => ?_⟩, hc, hk, hck⟩
  obtain ⟨hne', hi, hcl⟩ := hV V hV' hne
  have hB := hA hZ _ hne'
  have : IsIntegral Z := hZ.1
  have : Nonempty (c ⁻¹ᵁ V) := hne'.to_subtype
  exact aic_of_int (c.app V).hom hB hi hcl inferInstance

end LateralTheory.E.SteinPf
