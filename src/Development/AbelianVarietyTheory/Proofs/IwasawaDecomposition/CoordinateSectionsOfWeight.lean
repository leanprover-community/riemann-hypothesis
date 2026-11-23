module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.ValCoord

open GlobalTheory.ShFam.Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_bc {A B : Type} [CommRing A] [CommRing B] {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (fr : EigFrame Z φ x)
    (ρ : A →+* B) {x' : Sp B ⟶ Z.X} (hx : spMap ρ ≫ x = x') :
    ∃ g : EigFrame Z (ρ.comp φ) x', ∀ τ i, g.v τ i = spMap (dualMap ρ) ≫ fr.v τ i := by
  subst hx
  exact GlobalTheory.T.exists_eigFrame_baseChange' E H Dw l Xo c O β Z A B φ x fr ρ

theorem spMap_dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (ρ : A →+* B) (χ : B →+* C) :
    spMap (dualMap χ) ≫ spMap (dualMap ρ) = spMap (dualMap (χ.comp ρ)) := by
  rw [sp_comp]
  congr 1
  ext z <;> simp [dualMap]

theorem tri_bc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {φ : c.F →+* A} {x : Sp A ⟶ Z.X}
    {fr : EigFrame Z φ x} {ρ : A →+* B} {x₀ : Sp B ⟶ Z.X} (hx₀ : spMap ρ ≫ x = x₀) {g₀ : EigFrame Z (ρ.comp φ) x₀}
    (hg : ∀ τ i, g₀.v τ i = spMap (dualMap ρ) ≫ fr.v τ i) {χ : B →+* C} {φ' : c.F →+* C} {x' : Sp C ⟶ Z.X}
    {g : EigFrame Z φ' x'} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Cˣ} (h : fr.Tri (χ.comp ρ) g t) : g₀.Tri χ g t := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun τ i => ?_⟩
  · rw [h1, ← hx₀, ← Category.assoc, sp_comp]
  · rw [h2]; rfl
  · obtain ⟨cf, c1, c2, c3⟩ := h3 τ i
    refine ⟨cf, c1, c2, ?_⟩
    have e : (fun k => spMap (dualMap χ) ≫ g₀.v τ k) = fun k => spMap (dualMap (χ.comp ρ)) ≫ fr.v τ k :=
      funext fun k => by rw [hg, ← Category.assoc, spMap_dualMap_comp]
    rw [e]
    exact c3

variable {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

end GlobalTheory.ShFam.ValCoord
