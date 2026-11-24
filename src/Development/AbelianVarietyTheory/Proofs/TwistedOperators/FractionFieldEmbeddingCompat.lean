module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FractionalBaseInclusion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.Proof.FractionFieldEmbeddingCompat

open Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion

theorem fracExt_fracBase_algebraMap {D : D7} (c : NChoice D) (w : D.what₂.places.Pl) (y : D.ntw.O0 (c.twI w)) :
    fracExt c w (fracBase D (c.twI w) (algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y)) =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
          (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y))) := by
  rw [← IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)]
  simp [fracExt, fracBase, IsFractionRing.map]

theorem embW_eq_of_tie {D : D7} {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) (x : D.LL0) :
    c.embW w (x : D.what₂.LL) = fracExt c w (fracBase D (c.twI w) (embSide D (c.twI w) (c.sd w) x)) := by
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w)) (embSide D (c.twI w) (c.sd w) x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hz0
  have hmul : embSide D (c.twI w) (c.sd w) x * algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z =
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y := by
    rw [← hyz, div_mul_cancel₀ _ hz1]
  have e := h.embedding_baseField_condition w x y z hz0 hmul
  rw [← fracExt_fracBase_algebraMap, ← fracExt_fracBase_algebraMap, ← hmul, map_mul, map_mul] at e
  exact mul_right_cancel₀ ((map_ne_zero _).2 ((map_ne_zero _).2 hz1)) e

theorem embCompat : EmbCompat := by
  intro D c h K _ _ _ κ hκ w ιK hι
  subst hι
  ext x
  have e := embW_eq_of_tie h w (κ x)
  rw [hκ x] at e
  exact e

end GlobalTheory.Proof.FractionFieldEmbeddingCompat

end
