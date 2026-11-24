module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

theorem isPullback_fromSpec_app_rank {X Y : Scheme.{0}} (π : X ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen (π ⁻¹ᵁ W)) :
    IsPullback hV.fromSpec (Spec.map (π.app W)) π hW.fromSpec :=
  (IsOpenImmersion.isPullback _ _ _ _ (by
    rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec π hW hV]) (by simp)).flip

theorem rankAtStalk_sec (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (Z : Scheme.{0}) (y : (functor A B r).obj (op Z)) (W : Z.affineOpens)
    (P : PrimeSpectrum Γ(Z, W)) : Module.rankAtStalk (Sec A B y W) P = r := by
  obtain ⟨_hfin, _hflat, h3⟩ := y.2.2
  have hW : IsAffineOpen (W : Z.Opens) := W.2
  have hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens)) := hW.preimage _
  haveI : Module.Finite Γ(Z, W) (Sec A B y W) := by
    have := IsFinite.finite_app (subStr A B y) (W : Z.Opens) hW
    exact this
  haveI : Module.Flat Γ(Z, W) (Sec A B y W) := by
    have := Scheme.Hom.flat_appLE (subStr A B y) hW hV le_rfl
    rw [Scheme.Hom.appLE_eq_app] at this
    exact this
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_fromSpec_app_rank (subStr A B y) hW hV) P
  rw [h3] at e
  rw [← Scheme.Hom.finrank_SpecMap_algebraMap]
  exact e

end GlobalTheory.HilbAff
