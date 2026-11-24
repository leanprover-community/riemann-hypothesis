module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
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

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem dbl_map_fold {P' P : Arrow Spc} (φ : P' ⟶ P) :
    dbl.map φ ≫ dbl.fold P = dbl.fold P' ≫ φ.right := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext
  · simp only [dbl.map, dbl.fold, pushout.map]
    erw [pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc, pushout.inl_desc_assoc]
    simp
  · simp only [dbl.map, dbl.fold, pushout.map]
    erw [pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc, pushout.inr_desc_assoc]
    simp

theorem LeafActNat_of : LeafActNat := by
  intro hA q _ P' P φ n m i j a b
  apply Subtype.ext
  have hc := (hA q).1 (dbl.map φ) (pull _ (dbl.fold P) (tw q i) n a) b.1
  change pull _ (dbl.map φ) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1 -
      pull _ (dbl.fold P) _ _ (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1))) =
    cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1) -
      pull _ (dbl.fold P') _ _ (pull _ (dbl.inr P') _ _
        (cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1)))
  have e1 : pull (ZMod q) (dbl.map φ) (tw q i) n (pull _ (dbl.fold P) _ n a) =
      pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a) := by
    rw [← pull_comp, ← pull_comp, dbl_map_fold]
  have hcc : pull (ZMod q) (dbl.map φ) (tw q (i + j)) (n + m) (cup q (pull _ (dbl.fold P) _ n a) b.1) =
      cup q (pull _ (dbl.fold P') _ n (pull _ φ.right _ _ a)) (pull _ (dbl.map φ) _ _ b.1) := by
    rw [hc, e1]
  rw [map_sub, hcc]
  congr 1
  rw [← hcc, ← pull_comp _ (dbl.map φ) (dbl.fold P), dbl_map_fold, pull_comp _ (dbl.fold P') φ.right,
    ← pull_comp _ φ.right (dbl.inr P), ← dbl.inr_map, pull_comp _ (dbl.inr P') (dbl.map φ)]

end LateralTheory.CohomologicalPurity.TubeCut
