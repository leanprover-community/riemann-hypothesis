module

public import Development.EtaleCohomology.EtaleSheaves.CupProductRingLaws
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.FirstChernNaturality

variable {R : Type} [CommRing R]

theorem chainsXIso_inv_nat {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  simp [chains, chainsXIso, chainsN, HomologicalComplex.extendMap_f]

theorem freeGen_nat {P P' : PSh} (g : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map g).hom.app (op U)).hom (freeGen R P U x) = freeGen R P' U (g.app (op U) x) := by
  have h := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map g))
  unfold freeGen
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology ((freeP R).obj P')).app (op U)).hom
    ((((freeP R).map g).app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) = _
  congr 1
  simp only [ModuleCat.freeMk, freeP]
  simp [ModuleCat.free]
  erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem ev_zpull {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (γ : Cocycle ((chains R).obj E') I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (zcomp (Cocycle.ofHom ((chains R).map f)) γ (zero_add n)).1 p s h U x =
      ev γ.1 p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x) := by
  have hc : (zcomp (Cocycle.ofHom ((chains R).map f)) γ (zero_add n)).1.v (-(p : ℤ)) s h =
      ((chains R).map f).f (-(p : ℤ)) ≫ γ.1.v (-(p : ℤ)) s h := by
    simp [zcomp, Cochain.comp_v _ _ (zero_add n) (-(p : ℤ)) (-(p : ℤ)) s (by simp) h]
  unfold ev
  rw [hc, ← Category.assoc, chainsXIso_inv_nat, Category.assoc]
  exact congrArg (((chainsXIso R E' p).inv ≫ γ.1.v (-(p : ℤ)) s h).hom.app (op U)).hom
    (freeGen_nat (f.app (op (SimplexCategory.mk p))) U x)

theorem sub_nat {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (f.app (op (SimplexCategory.mk l))).app (op U) (x.sub j l h) =
      Sx.sub (E := E') ((f.app (op (SimplexCategory.mk N))).app (op U) x) j l h := by
  unfold Sx.sub
  exact congrFun (congrArg (fun t => t.app (op U)) (f.naturality (SimplexCategory.subinterval j l h).op)) x

theorem lineUnit_comp {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 1 U) :
    lineUnit (f ≫ L) x = lineUnit L ((f.app (op (SimplexCategory.mk 1))).app (op U) x) := rfl

theorem etale_first_chern_class_natural_of_spec (hC1 : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassRepresentedByChernCocycle) : LateralTheory.E.CupProductRingLaws.EtaleFirstChernClassNaturalUnderPullback := by
  intro q _ E E' f L hinv
  have hinvE : Inv q E := fun U ⟨x⟩ => hinv U ⟨(f.app _).app _ x⟩
  obtain ⟨⟨γ, hγ⟩, h2⟩ := hC1 q L hinv
  rw [h2 γ hγ]
  obtain ⟨_, h2'⟩ := hC1 q (f ≫ L) hinvE
  rw [h2' (zcomp (Cocycle.ofHom ((chains _).map f)) γ (zero_add 2)) ?_]
  · rfl
  obtain ⟨g0, g1, g2⟩ := hγ
  refine ⟨?_, ?_, ?_⟩
  · intro U x
    rw [ev_zpull]; exact g0 U _
  · intro U x v hv
    rw [ev_zpull]; exact g1 U _ v (by rw [hv, lineUnit_comp])
  · intro U x v w hv hw
    rw [ev_zpull]
    exact g2 U _ v w (by rw [hv, lineUnit_comp, sub_nat]) (by rw [hw, lineUnit_comp, sub_nat])

end LateralTheory.E.FirstChernNaturality
