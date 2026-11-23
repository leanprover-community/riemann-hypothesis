module

public import Development.EtaleCohomology.TateTwists.EtaleSimplicialChainsFreeDescription
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ChainsBasicPf

variable (R : Type) [CommRing R]

lemma chainsN_d (E : Spc) (p : ℕ) :
    ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ p

lemma chains_map_f {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    ((chains R).map f).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv :=
  HomologicalComplex.extendMap_f _ _ rfl

lemma chains_d (E : Spc) (p : ℕ) :
    ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ ((chainsN R).obj E).d (p + 1) p ≫ (chainsXIso R E p).inv :=
  HomologicalComplex.extend_d_eq _ _ rfl rfl

lemma chains_d' (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom =
      ((chainsN R).obj E).d (p + 1) p := by
  rw [chains_d R E p]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma chains_le (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

end LateralTheory.EtaleFoundations.ChainsBasicPf

open LateralTheory.EtaleFoundations.ChainsBasicPf in
theorem LateralTheory.EtaleFoundations.etale_simplicial_chains_basic_properties_hold : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := by
  intro R _
  refine ⟨fun E => chains_le R E, fun {E E'} f p => ?_, fun E p => ?_⟩
  · rw [chains_map_f R f p]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [chains_d' R E p]
    exact chainsN_d R E p
