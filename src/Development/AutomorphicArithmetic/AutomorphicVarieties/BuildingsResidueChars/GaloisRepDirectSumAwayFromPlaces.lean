module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepSumRepAwayFromLHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open UpperTheory.V.Af UpperTheory.V.Af.Gu
open GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.SumParam

theorem UpperTheory.galoisRep_direct_sum_away_from_places :
    SumAway := by
  intro E Ω _ _ _ _ _ l _ ι a b r r' hr hr' w hl A h x x' hx hx'
  have c : Continuous fun g => ((r g : GL (Fin a) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin a) (Fin a) (Formalism.ConjugateSelfDual.Qbar l)) :=
    Units.continuous_val.comp hr
  have c' : Continuous fun g => ((r' g : GL (Fin b) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin b) (Fin b) (Formalism.ConjugateSelfDual.Qbar l)) :=
    Units.continuous_val.comp hr'
  have cs : Continuous fun g => ((Formalism.MainNotions.SumRepresentations.At.sumRep r r' g : GL (Fin (a + b)) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin (a + b)) (Fin (a + b)) (Formalism.ConjugateSelfDual.Qbar l)) := by
    simp only [coe_sumRep]
    exact (c.matrix_fromBlocks continuous_const continuous_const c').matrix_reindex _ _
  rw [← hx.wdOf_eq hl, ← hx'.wdOf_eq hl, ← wdOf_sumRep hl ι r r' c c']
  exact isWDOf_wdOf hl ι cs
