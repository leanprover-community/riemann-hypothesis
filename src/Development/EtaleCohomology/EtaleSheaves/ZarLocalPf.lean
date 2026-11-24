module

public import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ZarLocalPf

def LocSH : Prop := ∀ (S : Type) [CommRing S], AIC S → ∀ p : PrimeSpectrum S, SH (Localization.AtPrime p.asIdeal)

def LocDiag : Prop := ∀ (S : Type) [CommRing S] (p : PrimeSpectrum S),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
    Nonempty (IsColimit c) ∧ (SH (Localization.AtPrime p.asIdeal) → SH c.pt) ∧
    ∃ (j0 : J) (a : S →+* D.obj j0), ∀ (k : J) (m : j0 ⟶ k), ∃ f : S, f ∉ p.asIdeal ∧
      ∃ r : D.obj k →+* Localization.Away f, r.comp ((D.map m).hom.comp a) = algebraMap S (Localization.Away f)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem ZarLocal_of (hSH : LocSH) (hD : LocDiag) : LateralTheory.E.t_E1Cut.ZarLocal := by
  intro hB1 hB2 q S _ hS hq n i hn x p
  obtain ⟨J, _, _, D, c, ⟨hc⟩, hpt, j0, a, hk⟩ := hD S p
  have hsh : SH c.pt := hpt (hSH S hS p)
  set y := pull _ (spMap a) _ _ x with hy
  have hqa : IsUnit ((q : ℕ) : D.obj j0) := by simpa using hq.map a
  have h0 : pull _ (spMap (c.ι.app j0).hom) _ _ y = 0 := by
    exact @Subsingleton.elim _ (hB2 (ZMod q) c.pt hsh (tw q i) n hn) _ _
  obtain ⟨k, m, hm⟩ := (hB1 q D c hc n i).2 j0 y hqa h0
  obtain ⟨f, hf, r, hr⟩ := hk k m
  refine ⟨f, hf, ?_⟩
  rw [← hr, spMap_comp, pull_comp, spMap_comp, pull_comp, ← hy, hm, map_zero]

end LateralTheory.E.ZarLocalPf
