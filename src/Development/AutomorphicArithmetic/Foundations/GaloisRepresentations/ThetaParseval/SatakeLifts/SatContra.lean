module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatConj
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

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.satContra :
    UpperTheory.Gal.TP.Loc.ContraUnit → UpperTheory.Gal.TP.Loc.SatContra := by
  intro hCU K _ _ w n V _ _ ρ hs hi hu B hB
  obtain ⟨-, C, hC⟩ := hCU (w.adicCompletion K) n V ρ hs hi hu
  obtain ⟨b, -, hp, hinv⟩ := hu
  refine UpperTheory.V.Af.Gk.satConj K n w V (smoothPart ρ.dual) ρ (contra ρ) b.flip C ?_ ?_ hC B hB
  · intro x hx
    by_contra h0
    have h1 := hp x h0
    have h2 : b x x = 0 := hx
    rw [h2] at h1
    simp at h1
  · intro g x y
    exact hinv g y x
