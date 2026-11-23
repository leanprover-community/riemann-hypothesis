module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAt
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAffineOpenSpecStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftsAgreeOfCocycleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCocycleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroLiftBasicOpenPairAgreeStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue

theorem lifts_corrected_agree_on_overlaps : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by
  intro R R₀ _ _ π hπ hI X hX g₀ hg₀ κ _ f hf V hV hL
  classical
  have : Fintype κ := Fintype.ofFinite κ
  choose e he1 he2 he3 using hL
  choose N₀ hN₀ using fun k j => GlobalTheory.T.exists_squareZeroLift_basicOpen_pair_agree R R₀ π hπ hI X hX g₀ hg₀ (f j) (f k) (V j) (hV j) (e j) (he1 j) (he2 j) (he3 j) (e k) (he1 k) (he2 k)
  have hN : ∀ k j, N₀ k j ≤ Finset.univ.sup (fun p : κ × κ => N₀ p.1 p.2) := fun k j =>
    Finset.le_sup (f := fun p : κ × κ => N₀ p.1 p.2) (Finset.mem_univ (k, j))
  choose t ht1 ht2 ht3 ht4 using fun k j => hN₀ k j _ (hN k j)
  choose n s W hs hW hWl using fun j l => GlobalTheory.T.exists_basicOpen_cover_affineOpen_spec _ _ (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j)
  obtain ⟨M, t', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_pow_cocycle_alt R R₀ π hπ hI X hX g₀ hg₀ κ f V hV e he1 he2 he3 _ t ht1 ht2 ht3 ht4 n s W hs hW hWl
  exact GlobalTheory.T.exists_lifts_agree_of_cocycle_alt R R₀ π hπ hI X g₀ hg₀ κ f hf V hV e he1 he2 he3 _ t' h1 h2 h3 n s W hs hW hWl h4

end GlobalTheory.SecGlue
