module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pMapOfIso :
    MapOfIso := by
  intro G₀ R _ _ gb S s N o o' θ hiso hmon hact hpol heta
  haveI : IsIso θ.left := (Over.forget S).map_isIso θ
  refine ⟨⟨θ.left, Hecke.sq2 θ, ⟨IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩, ?_⟩, ⟨?_, ?_⟩,
    fun c => ?_, hpol, fun y => ?_⟩, rfl⟩
  · intro T x y x₀ y₀ hx hy
    let u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have ex : x₀ = u ≫ x ≫ θ := Over.OverMorphism.ext (by simp [u, hx])
    have ey : y₀ = u ≫ y ≫ θ := Over.OverMorphism.ext (by simp [u, hy])
    rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
    simp [u]
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  · rw [← Over.comp_left, hact c, Over.comp_left]
  · rw [← Over.comp_left, heta y, Category.id_comp]
