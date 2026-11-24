module

public import Development.EtaleCohomology.CohomologicalPurity.LeafExcFormalPf
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

theorem HK.pull_sub' (R : Type) [CommRing R] {K L : Cx R} (f g : K ⟶ L) (F : Shv R) (n : ℤ)
    (x : HK R L F n) : HK.pull R (f - g) F n x = HK.pull R f F n x - HK.pull R g F n x := by
  rcases x.mk_surjective with ⟨z, rfl⟩
  simp only [HK.pull, HK.pre, cpre_mk]
  rw [← CohomologyClass.mk_sub]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_sub, Cochain.sub_comp]

theorem HK.pull_zero' (R : Type) [CommRing R] {K L : Cx R} (F : Shv R) (n : ℤ)
    (x : HK R L F n) : HK.pull R (0 : K ⟶ L) F n x = 0 := by
  have h := HK.pull_sub' R (0 : K ⟶ L) 0 F n x
  rw [sub_self, sub_self] at h
  exact h

def secC (q : ℕ) (P : Arrow Spc) :
    cokernel ((chains (ZMod q)).map (dbl.inr P)) ⟶ (chains (ZMod q)).obj (dbl P) :=
  cokernel.desc _ (𝟙 _ - (chains (ZMod q)).map (dbl.fold P) ≫ (chains (ZMod q)).map (dbl.inr P)) (by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, ← Functor.map_comp, dbl.inr_fold,
      CategoryTheory.Functor.map_id, Category.id_comp, sub_self])

theorem pi_secC (q : ℕ) (P : Arrow Spc) :
    cokernel.π ((chains (ZMod q)).map (dbl.inr P)) ≫ secC q P =
      𝟙 _ - (chains (ZMod q)).map (dbl.fold P) ≫ (chains (ZMod q)).map (dbl.inr P) := by
  simp [secC]

theorem secC_pi (q : ℕ) (P : Arrow Spc) :
    secC q P ≫ cokernel.π ((chains (ZMod q)).map (dbl.inr P)) = 𝟙 _ := by
  rw [← cancel_epi (cokernel.π _), ← Category.assoc, pi_secC, Category.comp_id, Preadditive.sub_comp,
    Category.id_comp, Category.assoc, cokernel.condition, Limits.comp_zero, sub_zero]

def eHom (q : ℕ) (n i : ℤ) (P : Arrow Spc) :
    HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n →+ Hs q P n i :=
  (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n).codRestrict _ fun x => by
    change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.inr P)) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) = 0
    rw [← HK.pull_comp', cokernel.condition, HK.pull_zero']

def eEquiv (q : ℕ) (n i : ℤ) (P : Arrow Spc) :
    HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hs q P n i where
  toFun := eHom q n i P
  invFun y := HK.pull (ZMod q) (secC q P) (tw q i) n y.1
  left_inv x := by
    change HK.pull (ZMod q) (secC q P) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) = x
    rw [← HK.pull_comp', secC_pi, HK.pull_id']
  right_inv y := by
    apply Subtype.ext
    change HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n
      (HK.pull (ZMod q) (secC q P) (tw q i) n y.1) = y.1
    have hy : HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.inr P)) (tw q i) n y.1 = 0 := y.2
    rw [← HK.pull_comp', pi_secC, HK.pull_sub', HK.pull_id', HK.pull_comp', hy, map_zero, sub_zero]
  map_add' := map_add _

theorem EtaleExcIdent : LeafExcIdent := by
  intro q n i
  refine ⟨eEquiv q n i, fun {P' P} φ x => ?_⟩
  apply Subtype.ext
  change HK.pull (ZMod q) ((chains (ZMod q)).map (dbl.map φ)) (tw q i) n
      (HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n x) =
    HK.pull (ZMod q) (cokernel.π ((chains (ZMod q)).map (dbl.inr P'))) (tw q i) n
      (HK.pull (ZMod q) (cokC q φ) (tw q i) n x)
  rw [← HK.pull_comp', ← HK.pull_comp']
  congr 2
  simp [cokC]

end LateralTheory.CohomologicalPurity
