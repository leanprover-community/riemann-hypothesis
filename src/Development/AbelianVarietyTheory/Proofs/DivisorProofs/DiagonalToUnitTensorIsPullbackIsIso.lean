module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem hom_to_topS_eq {Rg : Type} [CommRing Rg] {Z : Over (Sp Rg)} (f g : Z ⟶ topS Rg) : f = g := by
  haveI : IsIso (topS Rg).hom := by
    show IsIso ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id, ← Scheme.topIso_hom]
    infer_instance
  ext1
  rw [← cancel_mono (topS Rg).hom, Over.w f, Over.w g]

def θOver {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : A ⟶ topS Rg ⊗ A :=
  lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A)

theorem θOver_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θOver A) := by
  refine ⟨⟨snd (topS Rg) A, ?_, ?_⟩⟩
  · rw [θOver, lift_snd]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, θOver, lift_fst, Category.id_comp]
      exact hom_to_topS_eq _ _
    · rw [Category.assoc, θOver, lift_snd, Category.comp_id, Category.id_comp]

theorem θ_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θ A) := by
  haveI := θOver_isIso A
  have : θ A = (Over.forget _).map (θOver A) := rfl
  rw [this]
  exact (Over.forget _).map_isIso (θOver A)

theorem θ_fA {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : θ A ≫ fA A = A.hom :=
  Over.w (θOver A)

theorem θ_pullback (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left)
    (p : X' ⟶ T) (t : T ⟶ Sp Rg) :
    (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧
      GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := by
  haveI := θ_isIso A
  refine ⟨fun h => ?_, θ_fA A, inferInstance⟩
  refine IsPullback.of_iso h (Iso.refl _) (asIso (θ A)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom]
    exact (θ_fA A).symm
  · simp

end GlobalTheory.HomFixUniv
