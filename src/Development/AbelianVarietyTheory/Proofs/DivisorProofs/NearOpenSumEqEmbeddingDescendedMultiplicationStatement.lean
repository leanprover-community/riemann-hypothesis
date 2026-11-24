module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairUOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenSumEqEmbeddingDescendedMultiplication
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.nearOpen_sum_eq_embedding_descendedMultiplication : ∀ {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G] (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left) (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom), (∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left → N.Pt s (v ≫ m) (x * y).left) → ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π), (DescKP.VT N V).ι ≫ (Desc.sum N p hp).left = DescKP.mT N V m hm ≫ (Desc.emb N p hp).left := by
  first | exact @GlobalTheory.Mum.DescKP.sum_eq_mT_emb | exact GlobalTheory.Mum.DescKP.sum_eq_mT_emb | (intros; apply GlobalTheory.Mum.DescKP.sum_eq_mT_emb <;> assumption)
