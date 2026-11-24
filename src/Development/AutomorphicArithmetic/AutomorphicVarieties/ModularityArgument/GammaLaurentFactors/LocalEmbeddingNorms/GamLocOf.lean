module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.HodgeTateFromSandwich
import Formalism.DoubleCosetMeasures.Statement
public import GroundTheory.AutomorphicForms.GL2.GJFEInduced
import GroundTheory.AutomorphicForms.GL2.GJFEInducedLevi
public import GroundTheory.AutomorphicForms.GL2.GJFELevi
import GroundTheory.AutomorphicForms.JacquetAdmissible
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet GroundTheory.Automorphic.GJStandardL
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem UpperTheory.V.Z.Gam.gamLocOf :
    UpperTheory.V.Z.Gam.GamLocOf := by
  intro hL hC hS K _ _ n _ v V _ _ π s hs
  have hirr : π.IsIrreducible := hs.isIrreducible
  have hsm : IsSmooth π := hs.isSmooth
  have hψ := GroundTheory.Global.continuous_localAdelicChar (K := K) v
  have hψ1 := GroundTheory.Global.localAdelicChar_ne_one (K := K) v
  obtain ⟨β, W, _, _, σ, hσirr, hσs, hσc, hσa, ι, hι⟩ := exists_embedding_parabolicInd (π := π) hsm
  obtain ⟨γ, hγ⟩ := exists_leviFE hσa hσc (inducedChar β) continuous_inducedChar
    (leviMeasure β (GroundTheory.Global.localAdelicChar K v)) hψ hψ1
  obtain ⟨P, c, j, h0, hd, hc, hγ'⟩ := hL _ n β W σ hσa hσirr hσc _ continuous_inducedChar _ _ hψ hψ1 γ hγ
  refine ⟨P, c, j, h0, ?_, hc, ?_⟩
  · rw [hd]
    exact (hS _ n V π s hs β W σ hσa hσirr hσc ι hι).symm
  · rw [← GroundTheory.Global.residueCard_adicCompletion, ← hγ']
    exact hC _ n V π hsm β W σ hσs ι hι _ _ hψ hψ1 γ (inducedFE_of_leviFE _ hψ hψ1 hγ)
