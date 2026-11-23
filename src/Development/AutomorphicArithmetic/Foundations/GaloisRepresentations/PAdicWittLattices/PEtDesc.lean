module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
open UpperTheory.Gal.Int.Geo (Lv Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pEtDesc :
    ExtPts → EtDesc := by
  intro hE W Z Y B _ c _ _ _ pZ pY _ f hf hpts
  haveI : Flat c := inferInstance
  haveI : EffectiveEpi c := inferInstance
  haveI : IsReduced (pullback c c) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst c c)
  have key : pullback.fst c c ≫ f = pullback.snd c c ≫ f := by
    refine hE pY _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, ← Category.assoc, pullback.condition]
    · intro Ω _ _ x
      refine hpts Ω (x ≫ pullback.fst c c) (x ≫ pullback.snd c c) ?_ |>.trans ?_ <;> simp [pullback.condition]
  refine ⟨inferInstance, EffectiveEpi.desc c f (fun {T} g₁ g₂ h => ?_), EffectiveEpi.fac _ _ _⟩
  have e₁ : pullback.lift g₁ g₂ h ≫ pullback.fst c c = g₁ := pullback.lift_fst _ _ _
  have e₂ : pullback.lift g₁ g₂ h ≫ pullback.snd c c = g₂ := pullback.lift_snd _ _ _
  calc g₁ ≫ f = pullback.lift g₁ g₂ h ≫ pullback.fst c c ≫ f := by rw [← Category.assoc, e₁]
    _ = pullback.lift g₁ g₂ h ≫ pullback.snd c c ≫ f := by rw [key]
    _ = g₂ ≫ f := by rw [← Category.assoc, e₂]
