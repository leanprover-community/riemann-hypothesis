module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullA

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

namespace GlobalTheory.CechDR.AffLoc

theorem eq_of_secMap_eq_on_pairs {X : Scheme.{0}} (B B' : Type) [CommRing B] [CommRing B']
    (x : Sp B ⟶ X) (ψ : Sp B' ⟶ Sp B) (a b : B')
    (h : ∀ (V' : (Sp B').affineOpens) (p : Pair x), V'.1 ≤ ψ ⁻¹ᵁ p.1.1.1 →
      (secMap (𝟙 (Sp B')) V'.1).hom a = (secMap (𝟙 (Sp B')) V'.1).hom b) : a = b := by
  have hex : ∀ y : Sp B', ∃ V' : (Sp B').affineOpens, y ∈ V'.1 ∧
      ∃ p : Pair x, V'.1 ≤ ψ ⁻¹ᵁ p.1.1.1 := by
    intro y
    obtain ⟨U, hU, hyU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x (ψ y)) trivial
    obtain ⟨V, hV, hyV, hVU⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Sp B) (U := x ⁻¹ᵁ U) (x := ψ y) hyU
    obtain ⟨W, hW, hyW, hWV⟩ :=
      exists_isAffineOpen_mem_and_subset (X := Sp B') (U := ψ ⁻¹ᵁ V) (x := y) hyV
    exact ⟨⟨W, hW⟩, hyW, ⟨(⟨V, hV⟩, ⟨U, hU⟩), hVU⟩, hWV⟩
  choose W hyW p hp using hex
  have key : (Scheme.ΓSpecIso (CommRingCat.of B')).inv a = (Scheme.ΓSpecIso (CommRingCat.of B')).inv b := by
    refine (Sp B').sheaf.eq_of_locally_eq' (fun y => (W y).1) ⊤ (fun _ => homOfLE le_top)
      (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyW y⟩) _ _ (fun y => ?_)
    have := h (W y) (p y) (hp y)
    simp only [secMap, Scheme.Hom.appLE, Scheme.Hom.id_app, CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  exact (Scheme.ΓSpecIso (CommRingCat.of B')).symm.commRingCatIsoToRingEquiv.injective key
end GlobalTheory.CechDR.AffLoc
