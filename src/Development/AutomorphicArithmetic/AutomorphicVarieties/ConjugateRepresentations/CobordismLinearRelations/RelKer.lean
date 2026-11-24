module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.CobLin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.SigCob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ZigClosed
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

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem cob_sub {Γ M : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] {ρ : Representation ℂ Γ M} {q : ℕ}
    {c c' : List Γ → M} (h : HCob ρ q c) (h' : HCob ρ q c') : HCob ρ q (c - c') := by
  have := UpperTheory.V.Cj.cobLin Γ M ρ q (-1) c' c h' h
  rwa [neg_smul, one_smul, neg_add_eq_sub] at this

private theorem cob_add {Γ M : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] {ρ : Representation ℂ Γ M} {q : ℕ}
    {c c' : List Γ → M} (h : HCob ρ q c) (h' : HCob ρ q c') : HCob ρ q (c + c') := by
  have := UpperTheory.V.Cj.cobLin Γ M ρ q 1 c c' h h'
  rwa [one_smul] at this

theorem UpperTheory.V.Cj.relKer :
    UpperTheory.V.Cj.RelKer := by
  intro E _ _ _ a ha U hU σ Ξ Ξ' h hσ q α β
  have hs := UpperTheory.V.Cj.sigCob E a U σ Ξ Ξ' h hσ q
  refine ⟨?_, fun a1 b1 a2 b2 a3 b3 => ?_⟩
  · rintro ⟨a1, b1, c, c', p, p', hc⟩
    rw [← perKer E a ha U hU Ξ q α c a1 p, ← perKer E a ha U hU Ξ' q β c' b1 p', ← hs c]
    constructor
    · intro k
      have := cob_add hc k
      rwa [sub_add_cancel] at this
    · intro k
      have := cob_sub k hc
      rwa [sub_sub_cancel] at this
  · obtain ⟨c, p⟩ := (perEx E a U Ξ q).1 α a1 a2
    obtain ⟨c', p'⟩ := (perEx E a U Ξ' q).1 β b1 b2
    exact ⟨a1, b1, c, c', p, p', cob_sub ((perKer E a ha U hU Ξ' q β c' b1 p').2 b3)
      ((hs c).2 ((perKer E a ha U hU Ξ q α c a1 p).2 a3))⟩
