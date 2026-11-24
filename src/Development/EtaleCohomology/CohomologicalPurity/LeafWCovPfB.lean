module

public import Development.EtaleCohomology.CohomologicalPurity.LeafWCovPf
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
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

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

def LeafPLoc : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), LocCov f g →
  ∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0}
    (biprod.desc ((freeP R).map (f.app n)) ((freeP R).map (g.app n)))

theorem LeafCovLoc_of (hP : LeafPLoc) : LeafCovLoc := by
  intro R _ U V E f g hf hg hL
  refine ⟨hf, hg, fun n => ?_⟩
  let S := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  let a := (freeP R).map (f.app n)
  let b := (freeP R).map (g.app n)
  have h1 : Epi (S.map (biprod.desc a b)) := by
    have : Sheaf.IsLocallySurjective (S.map (biprod.desc a b)) :=
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff _ _).2 (hP R f g hL n)
    infer_instance
  change Epi (biprod.desc (S.map a) (S.map b))
  let P := (freeP R).obj (U.obj n) ⊞ (freeP R).obj (V.obj n)
  let k : S.obj P ⟶ S.obj ((freeP R).obj (U.obj n)) ⊞ S.obj ((freeP R).obj (V.obj n)) :=
    biprod.lift (S.map (biprod.fst : P ⟶ _)) (S.map (biprod.snd : P ⟶ _))
  have h2 : k ≫ biprod.desc (S.map a) (S.map b) = S.map (biprod.desc a b) := by
    simp only [k]
    rw [biprod.lift_desc, ← S.map_comp, ← S.map_comp, ← S.map_add (f := _), biprod.desc_eq]
  rw [← h2] at h1
  exact epi_of_epi k _

theorem LeafWCov_of' (hG : LeafGeo) (hP : LeafPLoc) (hW : LeafWLoc) : LeafWCov :=
  LeafWCov_of hG (LeafCovLoc_of hP) hW

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
