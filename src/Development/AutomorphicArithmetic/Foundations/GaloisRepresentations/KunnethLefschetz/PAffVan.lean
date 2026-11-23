module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
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
import Mathlib.Tactic.Linter.Style
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem sub_of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (q : ℕ) (n i : ℤ)
    (h : Subsingleton (Ht q (sp A) n i)) : Subsingleton (Ht q (sp B) n i) := by
  have hid : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 (sp B) := by
    simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by
      ext x
      simp
    rw [this]
    simp
  refine ⟨fun x y => ?_⟩
  have hx : x = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x) := by
    rw [← pull_comp, hid, pull_id]
  have hy : y = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y) := by
    rw [← pull_comp, hid, pull_id]
  rw [hx, hy, Subsingleton.elim (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x)
    (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y)]

theorem UpperTheory.Gal.KunnethLefschetz.affVan_holds :
    UpperTheory.Gal.KunnethLefschetz.AffVan := by
  intro hIn hPt k _ _ q _ hq d n i hn
  show Subsingleton (Ht q (sp (MvPolynomial (Fin d) k)) n i)
  induction d with
  | zero =>
    have h0 : Subsingleton (Ht q (sp k) n i) := hPt hIn k q n i hn
    exact sub_of_equiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm q n i h0
  | succ d ih =>
    have hq' : IsUnit ((q : ℕ) : MvPolynomial (Fin d) k) := by
      have := hq.map (MvPolynomial.C : k →+* MvPolynomial (Fin d) k)
      rwa [map_natCast] at this
    have hpoly : Subsingleton (Ht q (sp (Polynomial (MvPolynomial (Fin d) k))) n i) := by
      have hb := hIn.c4 q (MvPolynomial (Fin d) k) hq' i n
      refine ⟨fun x y => ?_⟩
      obtain ⟨a, rfl⟩ := hb.2 x
      obtain ⟨b, rfl⟩ := hb.2 y
      rw [Subsingleton.elim a b]
    exact sub_of_equiv (MvPolynomial.finSuccEquiv k d).toRingEquiv.symm q n i hpoly
