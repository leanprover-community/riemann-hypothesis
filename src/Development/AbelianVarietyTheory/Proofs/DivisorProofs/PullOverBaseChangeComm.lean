module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pull_over_baseChange_comm : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A Y : Over (Sp R)) (A' Y' : Over (Sp R')) (f : Y ⟶ A) (f' : Y' ⟶ A') (φ : A'.left ⟶ A.left) (ψ : Y'.left ⟶ Y.left) (hA : φ ≫ A.hom = A'.hom ≫ spMap σ) (hY : ψ ≫ Y.hom = Y'.hom ≫ spMap σ), f'.left ≫ φ = ψ ≫ f.left → (∀ x, pullHO1 hY (pO1 f x) = pO1 f' (pullHO1 hA x)) ∧ ∀ x, pullHO2 hY (structureSheafH2Pullback f x) = structureSheafH2Pullback f' (pullHO2 hA x) := by
  intro R R' _ _ σ A Y A' Y' f f' φ ψ hA hY hcomm
  have hχ : (ψ ≫ f.left) ≫ A.hom = Y'.hom ≫ spMap σ := by
    rw [Category.assoc, Over.w f, hY]
  have H := (GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1
  refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩
  · have e1 := (H R R A.left Y.left A.hom Y.hom (RingHom.id R) f.left (ovw f) R'
      Y'.left Y'.hom σ ψ hY σ (ψ ≫ f.left) hχ rfl (fun _ ↦ rfl)).1 x
    have e2 := (H R R' A.left A'.left A.hom A'.hom σ φ hA R' Y'.left Y'.hom
      (RingHom.id R') f'.left (ovw f') σ (ψ ≫ f.left) hχ hcomm.symm (fun _ ↦ rfl)).1 x
    simp only [pO1]
    rw [e1, e2]
  · have e1 := (H R R A.left Y.left A.hom Y.hom (RingHom.id R) f.left (ovw f) R'
      Y'.left Y'.hom σ ψ hY σ (ψ ≫ f.left) hχ rfl (fun _ ↦ rfl)).2.1 x
    have e2 := (H R R' A.left A'.left A.hom A'.hom σ φ hA R' Y'.left Y'.hom
      (RingHom.id R') f'.left (ovw f') σ (ψ ≫ f.left) hχ hcomm.symm (fun _ ↦ rfl)).2.1 x
    simp only [structureSheafH2Pullback]
    rw [e1, e2]

end GlobalTheory.AbCoh
