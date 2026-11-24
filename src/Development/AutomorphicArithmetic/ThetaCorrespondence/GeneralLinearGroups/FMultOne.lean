module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FPiece
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MCellone
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

theorem UpperTheory.Lit.Full.multOne :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : Set (IrrGL (k := k))) (y z : IrrGL (k := k)) (N : ℕ) (hd : ∑ a, (![y, z] a).1 = N), SuppIn y P → FirstIn z Pᶜ → jm ![y, z] hd (prodIrr ![y, z] hd) ≤ 1 := by
  intro hG hBZ k _ _ _ _ P y z N hd hy hz
  refine UpperTheory.Lit.Mix.cellone hG hBZ k y z N hd fun q hq hpos hjm p hc => ?_
  by_contra hne
  obtain ⟨A, hA, hAP⟩ := hy
  obtain ⟨B, hB, w, hwB, hwP⟩ := (UpperTheory.Lit.Full.piece hG hBZ k z Pᶜ q hq hjm).1 hz hpos
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG p
  have ht : ∀ a, HasSupport (![p, q 0] a).rep (![C, B] a) := fun a => by
    fin_cases a
    · exact hC
    · exact hB
  have hS := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (hd := hc) ht y.2.rep.irr
    (jhMult_ne_zero_iff.1 hne)
  have hE := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hA hS
  refine hwP (hAP w ?_)
  rw [hE, Fin.sum_univ_two]
  exact Multiset.mem_add.2 (Or.inr hwB)
