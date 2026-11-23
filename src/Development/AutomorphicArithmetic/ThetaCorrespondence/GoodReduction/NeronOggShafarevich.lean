module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTorsionUnramifiedOfTateModuleUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedImpTateModuleAndInfiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedOfHasGoodReductionStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.HasGoodReductionOfInfiniteTorsionUnramified
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.Nos
open GlobalTheory

theorem neronOggShafarevich : NeronOggShafarevichSt := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA
  tfae_have 1 → 2 := GlobalTheory.T.torsionUnramified_of_hasGoodReduction_alt R K Ω V hV A
  tfae_have 2 → 4 := fun hb => (GlobalTheory.T.torsionUnramified_imp_tateModule_and_infinite R K Ω V A hb).1
  tfae_have 2 → 3 := fun hb => (GlobalTheory.T.torsionUnramified_imp_tateModule_and_infinite R K Ω V A hb).2
  tfae_have 4 → 3 := by
    rintro ⟨l, hf, hl, ht⟩
    exact GlobalTheory.T.infinite_torsionUnramified_of_tateModuleUnramified R K Ω V hV A hA l hl ht
  tfae_have 3 → 1 := UpperTheory.Lit.Nos.C6.hasGoodReduction_of_infinite_torsionUnramified R K Ω V hV A hA
  tfae_finish

end UpperTheory.Lit.Nos.Nos
