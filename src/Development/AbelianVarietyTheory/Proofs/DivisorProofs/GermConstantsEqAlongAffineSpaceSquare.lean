module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
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

namespace GlobalTheory.FormsLocus

theorem germ_cstT_eq_germ_ringOf_C : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (n : ℕ) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg n → ∀ (z : X) (r : Rg), gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f r) = gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g (MvPolynomial.C r)) := by
  intro Rg _ A₀ T X f n g φ p h z r
  have e0 : (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
  have e1 : gs φ z ⊤ (cstT f r) = gs (φ ≫ f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) :=
    gs_pull φ f z ⊤ trivial _
  have h1 := gs_pull (p ≫ g) (affπ Rg n) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r)
  have h2 := gs_pull p g z ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r))
  rw [Category.assoc] at h1
  rw [e1, h, ← h1]
  refine Eq.trans ?_ h2.symm
  change gs (p ≫ g) z ⊤ ((affπ Rg n).appTop _) = _
  rw [e0]

end GlobalTheory.FormsLocus
