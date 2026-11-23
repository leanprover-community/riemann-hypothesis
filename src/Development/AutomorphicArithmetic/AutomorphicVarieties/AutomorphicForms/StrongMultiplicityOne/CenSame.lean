module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.cenSame :
    UpperTheory.V.Af.Smo.CentEq → UpperTheory.V.Af.StrongMultiplicityOne.SetUp → UpperTheory.V.Af.StrongMultiplicityOne.CenSame := by
  intro hC hS E _ _ n U U' hU hs hc φ' hφ' s g'
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  obtain ⟨S, B, hB, hk, hk'⟩ := hS E n U U' hs φ φ'
  have loc : ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), InKS S (locGL E n w k) := by
    intro w hw k hkk
    refine ⟨fun x hx => GlobalTheory.CuspRep.pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _, fun x => ?_⟩
    by_cases e : x = w
    · subst e
      rw [GlobalTheory.CuspRep.pLoc_locGL]
      exact hkk
    · rw [GlobalTheory.CuspRep.pLoc_locGL_of_ne e]
      exact one_mem _
  have e := hC E n S B φ.1 φ'.1 φ.2.1.continuous φ'.2.1.continuous φ.2.1.isLeftInvariant φ'.2.1.isLeftInvariant
    (fun w hw => ⟨(hB w hw).2.1 φ hφ fun g k h => hk g _ (loc w hw k h),
      (hB w hw).2.2 φ' hφ' fun g k h => hk' g _ (loc w hw k h)⟩) hk hk'
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  obtain ⟨z, hz⟩ : ∃ z : (Ad E)ˣ, Reduction.centralSection E n s = GeneralLinearGroup.scalar (Fin n) z :=
    ⟨_, Units.ext rfl⟩
  have e1 := e z g g'
  rw [← hz, apply_mul_centralSection_of_mem (hc hφ)] at e1
  rw [Reduction.centralSection_mul_comm]
  exact (mul_left_cancel₀ hg e1).symm
