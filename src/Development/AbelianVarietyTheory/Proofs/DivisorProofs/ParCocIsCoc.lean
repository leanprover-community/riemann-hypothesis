module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
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
import Mathlib.RingTheory.PiTensorProduct
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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem parCoc_isCoc : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (K : Type) (W : K → (A ⊗ B).left.Opens) (J : Type) [Fintype J] (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)), (∀ i, IsCoc (whole A) (a i)) → (∀ i, IsCoc (whole B) (b i)) → IsCupCob W a b n → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsCoc (parCov W x) (parCoc a b n x) := by
  intro R _ A B K W J _ a b n ha hb hn D _ _ x
  unfold IsCoc at ha hb ⊢
  unfold IsCupCob at hn
  intro E _ _ E' _ _ E'' _ _ φ ψ z hz
  have hz' : Sm W (z ≫ x ▷ B) := by
    unfold Sm at hz ⊢
    obtain ⟨k, hk⟩ := hz
    refine ⟨k, ?_⟩
    simpa [parCov, Over.comp_left, Scheme.Hom.comp_preimage] using hk
  have h1 := hn E E' E'' φ ψ (z ≫ x ▷ B) hz'
  have hfst : (z ≫ x ▷ B) ≫ fst _ _ = spOver (ptAlg (z ≫ fst _ _)) ≫ x := by
    rw [Category.assoc, whiskerRight_fst, ← Category.assoc, spOver_ptAlg]
  have hα : ptAlg ((spOver φ ≫ z) ≫ fst _ _) = φ.comp (ptAlg (z ≫ fst _ _)) := by
    rw [Category.assoc, ptAlg_comp]
  have ha' := fun i ↦ ha i D E E' (ptAlg (z ≫ fst _ _)) φ x (sm_whole _)
  have hb' := fun i ↦ hb i E E' E'' φ ψ (z ≫ snd _ _) (sm_whole _)
  rw [hfst] at h1
  simp only [Category.assoc, whiskerRight_snd] at h1
  simp only [parCoc]
  rw [hα]
  simp only [ha', hb', Category.assoc]

  simp only [map_sub, map_sum, map_mul, map_add (f := _), AlgHom.comp_apply, add_mul, mul_add, Finset.sum_add_distrib]
  linear_combination -h1

end GlobalTheory.PtExt
