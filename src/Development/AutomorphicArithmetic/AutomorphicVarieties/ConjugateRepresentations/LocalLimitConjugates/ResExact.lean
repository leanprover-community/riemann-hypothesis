module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.DelLev
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.KugaSm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevLin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SqOrth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.resExact :
    UpperTheory.V.Cj.H.ResExact := by
  intro E _ _ _ a ha n e he U Ξ r c hc q ω hω hd
  obtain ⟨k0, k1⟩ := kugaSm E a n e he Ξ r c hc
  cases q with
  | zero => exact ⟨k0 ω hω.equiv hd, fun _ _ => trivial⟩
  | succ q =>
    have hk := k1 q ω hω.equiv hd
    obtain ⟨d1, d2⟩ := delLev E a n e he U Ξ r q ω
    obtain ⟨l1, l2, -⟩ := levLin E a U Ξ q
    have hl := d1 hω
    refine ⟨⟨(-1 : ℂ) • del (smAdj Ξ r) e ω + (0 : ℂ) • del (smAdj Ξ r) e ω, l1 _ _ _ _ hl hl, ?_⟩, fun hs h0 => ?_⟩
    · rw [l2, hk, zero_smul, add_zero]
      exact AlternatingMap.ext fun X => neg_one_smul ℂ _
    · rw [hk, neg_eq_zero] at h0
      exact (sqOrth E a ha n e he Ξ r q).2 ω hs (d2 hs) h0
