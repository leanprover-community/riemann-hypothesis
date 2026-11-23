module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsAdditiveLiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullbackChStatement
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

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem ptAlg_apply_of_left {R D E : Type} [CommRing R] [CommRing D] [Algebra R D] [CommRing E] [Algebra R E]
    (z : Pt (SpAlg R D) E) (f : D →+* E) (h : z.left = spMap f) (a : D) : ptAlg z a = f a := by
  change (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left).hom a = f a
  rw [h, Spec.preimage_map]
  rfl

end GlobalTheory.PtExt

theorem GlobalTheory.PtExt.bcPull_sumMul_fv : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D]
    (B : Over (Sp R)) (B' : Over (Sp D)) (q : B'.left ⟶ (SpAlg R D ⊗ B).left)
    (w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D)) (π : B'.left ⟶ B.left),
    q ≫ (fst (SpAlg R D) B).left = B'.hom → q ≫ (snd (SpAlg R D) B).left = π →
    ∀ (mB : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 D) (B'.hom ≫ 𝟙 _) (algebraMap R D) π)
      (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))),
      bcPull w (sumMul d fun i ↦ fv (X := B) (β i)) =
        fv (X := B') (∑ i, d i • mB.coef.pullbackOneCocycle (β i)) := by
  classical
  intro R D _ _ _ B B' q w π hfst hsnd mB J _ d β
  have w' : π ≫ B.hom = B'.hom ≫ spMap (algebraMap R D) := by
    rw [← hsnd, Category.assoc, Over.w (snd (SpAlg R D) B), w]
  obtain ⟨hadd, hsmul, -⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear D B'
  funext E i1 i2 E' i3 i4 ψ y
  have hzero : fv (X := B') 0 E E' ψ y = 0 := by
    have h := congrArg (fun u : Fn1 B' ↦ u E E' ψ y) (hadd 0 0)
    simp only [add_zero, Fn1.add] at h
    linear_combination -h
  have hsum : ∀ s : Finset J, fv (X := B') (∑ i ∈ s, d i • mB.coef.pullbackOneCocycle (β i)) E E' ψ y =
      ∑ i ∈ s, algebraMap D E' (d i) * fv (X := B') (mB.coef.pullbackOneCocycle (β i)) E E' ψ y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      have h := congrArg (fun u : Fn1 B' ↦ u E E' ψ y) (hadd (d j • mB.coef.pullbackOneCocycle (β j)) (∑ i ∈ s, d i • mB.coef.pullbackOneCocycle (β i)))
      simp only [Fn1.add] at h
      rw [h, ih, hsmul]
  rw [hsum]
  simp only [bcPull, sumMul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback_changeOfBase R D (algebraMap R D) B B' π w' mB (β i)]
  congr 1
  · let _ : Algebra R E := algVia (algebraMap R D) E
    have hl : (ptVia w y ≫ fst (SpAlg R D) B).left = spMap (algebraMap D E) := by
      rw [Over.comp_left]
      change (y.left ≫ q) ≫ (fst (SpAlg R D) B).left = _
      rw [Category.assoc, hfst]
      exact Over.w y
    rw [ptAlg_apply_of_left _ _ hl]
    exact ψ.commutes (d i)
  · simp only [bcPull]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    change (y.left ≫ q) ≫ (snd (SpAlg R D) B).left = y.left ≫ π
    rw [Category.assoc, hsnd]
