module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
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
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChowCut

def Img : Prop := ∀ (A : Type) [CommRing A] {Z X : Scheme.{0}} (h : Z ⟶ X) (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p],
  IsIntegralHom h → IsIntegral Z → ∃ (X₁ : Scheme.{0}) (h₁ : Z ⟶ X₁) (p₁ : X₁ ⟶ Spec (CommRingCat.of A)),
    IsIntegral X₁ ∧ IsProper p₁ ∧ IsIntegralHom h₁ ∧ IsDominant h₁ ∧ h₁ ≫ p₁ = h ≫ p

def ChowL : Prop := ∀ (A : Type) [CommRing A] {X₁ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of A)) [IsProper p₁],
  IsIntegral X₁ → ∃ (X' : Scheme.{0}) (π : X' ⟶ X₁) (U : X₁.Opens) (s : U.toScheme ⟶ X'),
    (U : Set X₁).Nonempty ∧ s ≫ π = U.ι ∧ IT π ∧ IT (π ≫ p₁)

def Norm : Prop := ∀ {Z W : Scheme.{0}} (f : W ⟶ Z) [QuasiSeparated f], AICSch Z →
  (∃ (U : Z.Opens) (s : U.toScheme ⟶ W), (U : Set Z).Nonempty ∧ s ≫ f = U.ι) →
  ∃ (Z' : Scheme.{0}) (v : Z' ⟶ W), IsIntegralHom v ∧ AICSch Z' ∧ IsDominant (v ≫ f)

theorem goal_of (hI : Img) (hC : ChowL) (hN : Norm) : LateralTheory.E.t_E2Cut.Chow := by
  intro A _ Z X h p _ hh hZ
  obtain ⟨X₁, h₁, p₁, hX₁, hp₁, hh₁, hd₁, e⟩ := hI A h p hh hZ.1
  have := hp₁
  have := hh₁
  have := hd₁
  obtain ⟨X', π, U, s, hU, hs, hπ, hπp⟩ := hC A p₁ hX₁
  obtain ⟨_, _⟩ := (hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip).qc
  have hU' : ((h₁ ⁻¹ᵁ U : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨x, hxU, y, rfl⟩ := h₁.denseRange.inter_open_nonempty _ U.isOpen hU
    exact ⟨y, hxU⟩
  have sec : ∃ (V : Z.Opens) (t : V.toScheme ⟶ pullback h₁ π), (V : Set Z).Nonempty ∧ t ≫ pullback.fst h₁ π = V.ι :=
    ⟨h₁ ⁻¹ᵁ U, pullback.lift (h₁ ⁻¹ᵁ U).ι ((h₁ ∣_ U) ≫ s) (by rw [Category.assoc, hs, morphismRestrict_ι]), hU',
      pullback.lift_fst _ _ _⟩
  obtain ⟨Z', v, hv, hZ', hd⟩ := hN (pullback.fst h₁ π) hZ sec
  refine ⟨Z', v ≫ pullback.fst h₁ π, hZ', hd, hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip |>.pre v hv, ?_⟩
  have : (v ≫ pullback.fst h₁ π) ≫ h ≫ p = (v ≫ pullback.snd h₁ π) ≫ π ≫ p₁ := by
    rw [← e, Category.assoc, reassoc_of% pullback.condition, Category.assoc]
  rw [this]
  exact hπp.pre _ inferInstance

end LateralTheory.E.ChowCut

end
