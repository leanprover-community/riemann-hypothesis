module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
noncomputable section

namespace GlobalTheory.HomFixPoint

theorem exists_affine_hom (Rg : Type) [CommRing Rg] (T : Scheme.{0}) (n : ℕ) (t : T ⟶ Sp Rg)
    (x : Fin n → Γ(T, ⊤)) :
    ∃ g : T ⟶ Sp (MvPolynomial (Fin n) Rg), g ≫ affπ Rg n = t ∧ ∀ i, coord g i = x i := by
  let φ : MvPolynomial (Fin n) Rg →+* Γ(T, ⊤) :=
    MvPolynomial.eval₂Hom (t.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of Rg)).inv.hom) x
  have key : ∀ p, (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv p) = φ p := by
    intro p
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply
      (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      Scheme.toSpecΓ_appTop]
    simp
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · apply ext_of_isAffine
    refine (Iso.cancel_iso_inv_left (Scheme.ΓSpecIso (CommRingCat.of Rg)) _ _).1 ?_
    ext r
    have n2 : (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) =
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, n2, key]
    simp [φ]
  · intro i
    unfold coord
    rw [key]
    simp [φ]

end GlobalTheory.HomFixPoint
