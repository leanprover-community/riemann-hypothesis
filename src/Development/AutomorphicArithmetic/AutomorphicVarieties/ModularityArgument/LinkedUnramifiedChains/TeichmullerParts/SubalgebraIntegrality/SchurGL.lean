module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import GroundTheory.AutomorphicForms.SmoothRepSchur
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
public import GroundTheory.AutomorphicForms.SmoothRep

@[expose] public section

open UpperTheory.V.Z.J.D

theorem UpperTheory.V.Z.J.D.schurGL :
    SchurGL := by
  intro L _ _ n w τ
  letI := τ.acg
  letI := τ.mod
  haveI : τ.ρ.IsIrreducible := τ.irred
  have hsm : GroundTheory.Automorphic.IsSmooth τ.ρ := τ.smooth
  refine ⟨τ.irred, fun f hf => ?_⟩
  let φ : Representation.IntertwiningMap τ.ρ τ.ρ :=
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext fun v => hf g v }
  obtain ⟨c, hc⟩ := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth hsm).2 φ
  exact ⟨c, LinearMap.ext fun v => (congrArg (fun h : Representation.IntertwiningMap τ.ρ τ.ρ => h v) hc).symm⟩
