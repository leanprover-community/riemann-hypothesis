module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
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

open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.rhoFrob :
    UpperTheory.V.Z.Kato.Joint.RhoFrob := by
  intro l _ Ω _ _ _ ι e S A W g χ hN _ hatt ρ hρ
  have h : ∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Formalism.ConjugateSelfDual.Qbar l)) = _ := fun s =>
    (hρ s).trans (GlobalTheory.RhoAdm.untw_val' e W χ s).symm
  refine ⟨?_, fun V hV => GlobalTheory.RhoAdm.untw_irr e W χ hN.irr V fun s v hv => ?_⟩
  · obtain ⟨S0, hS0⟩ := GlobalTheory.RhoAdm.frob_trace_det ι e W g χ hatt
    refine ⟨S0, fun q hq hqS s hs => ?_⟩
    rw [h s]
    exact hS0 q hq hqS s hs
  · rw [← h s]
    exact hV s v hv
