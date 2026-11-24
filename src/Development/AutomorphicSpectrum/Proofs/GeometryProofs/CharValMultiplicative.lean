module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusPoints

theorem charVal_eq_diag {S : Scheme.{0}} {X : Type} [AddCommGroup X] {A : Type} [CommRing A] {a : Sp A ⟶ S}
    (t : Over.mk a ⟶ splitTorus S X) (χ : X) : charVal t χ = GlobalTheory.Diag.charVal t χ := by
  rw [GlobalTheory.Diag.charVal_eq_torusFst]
  rfl

theorem main : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] (a : Sp A ⟶ S), (∀ t t' : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = charVal t' χ) → t = t') ∧ (∀ (t t' : Over.mk a ⟶ splitTorus S X) (χ : X), charVal (t * t') χ = charVal t χ * charVal t' χ) ∧ (∀ χ : X, charVal (1 : Over.mk a ⟶ splitTorus S X) χ = 1) ∧ (∀ (t : Over.mk a ⟶ splitTorus S X), charVal t 0 = 1 ∧ ∀ χ χ', charVal t (χ + χ') = charVal t χ * charVal t χ') ∧ (∀ w : Multiplicative X →* A, ∃ t : Over.mk a ⟶ splitTorus S X, ∀ χ, charVal t χ = w (Multiplicative.ofAdd χ)) ∧ ∀ (A' : Type) [CommRing A'] (g : A →+* A') (t : Over.mk a ⟶ splitTorus S X) (t' : Over.mk (spMap g ≫ a) ⟶ splitTorus S X), t'.left = spMap g ≫ t.left → ∀ χ, charVal t' χ = g (charVal t χ) := by
  intro S X _ A _ a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t t' h
    refine GlobalTheory.Diag.charVal_ext fun χ => ?_
    rw [← charVal_eq_diag, ← charVal_eq_diag]
    exact h χ
  · intro t t' χ
    rw [charVal_eq_diag, charVal_eq_diag, charVal_eq_diag, GlobalTheory.Diag.charVal_mul]
  · intro χ
    rw [charVal_eq_diag, GlobalTheory.Diag.charVal_one]
  · intro t
    refine ⟨?_, fun χ χ' => ?_⟩
    · rw [charVal_eq_diag, GlobalTheory.Diag.charVal_zero]
    · rw [charVal_eq_diag, charVal_eq_diag, charVal_eq_diag, GlobalTheory.Diag.charVal_add]
  · intro w
    refine ⟨GlobalTheory.Diag.ofVal a w, fun χ => ?_⟩
    rw [charVal_eq_diag, GlobalTheory.Diag.charVal_ofVal]
  · intro A' _ g t t' ht χ
    rw [charVal_eq_diag, charVal_eq_diag]
    exact (GlobalTheory.Diag.left_eq_iff g rfl t' t).1 ht χ

end GlobalTheory.CompanionTheory.Ar.TorusPoints
