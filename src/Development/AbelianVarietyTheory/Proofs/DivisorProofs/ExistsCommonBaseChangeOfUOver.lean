module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem exists_common_baseChange_of_uOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (K R R' : Type) [Field K] [CommRing R] [CommRing R'] (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (σ : R →+* K) (σ' : R' →+* K) (u : Sp K ⟶ Xo.XF cf), UOver Xo cf P σ u → UOver Xo cf P' σ' u → ∃ (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsGrpPullback P₀.A P.A (spMap σ) a ∧ IsGrpPullback P₀.A P'.A (spMap σ') a' ∧ LBIso P₀.L (P.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') := by
  intro E _ _ _ H Dw l Xo cf K R R' _ _ _ P P' σ σ' u h h'
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  obtain ⟨G', _, α', β', hα', hβ', hL'⟩ := h'
  obtain ⟨P₀, φ, hφ, hLφ⟩ := exists_pol_baseChange P (spMap σ)
  obtain ⟨e₀, _, he₀⟩ := grpPullback_iso hφ hα
  obtain ⟨e, _, he⟩ := grpPullback_iso hβ hβ'
  haveI : IsMonHom (e₀ ≪≫ e).hom := inferInstanceAs (IsMonHom (e₀.hom ≫ e.hom))
  have hU := Xo.univ.t.PP.isLB
  have X1 : LBIso (P.L.pull φ) (Xo.univ.t.PP.L.pull (e₀.hom.left ≫ β)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp e₀.hom.left he₀.symm rfl hL
  have X2 : LBIso (Xo.univ.t.PP.L.pull (e₀.hom.left ≫ β)) (P'.L.pull ((e₀.hom.left ≫ e.hom.left) ≫ α')) :=
    GlobalTheory.GenSpread.lbIso_pull_comp (e₀.hom.left ≫ e.hom.left) (by rw [← he, Category.assoc]) rfl hL'.symm
  refine ⟨P₀, φ, (e₀.hom.left ≫ e.hom.left) ≫ α', hφ,
    ((isGrpPullback_of_iso (e₀ ≪≫ e)).comp hα').congr (Category.id_comp _) rfl, hLφ,
    LBIso.trans P₀.isLB (pull_isLB P.isLB _) (pull_isLB P'.isLB _) hLφ
      (LBIso.trans (pull_isLB P.isLB _) (pull_isLB hU _) (pull_isLB P'.isLB _) X1 X2)⟩

end GlobalTheory.UPoinc
