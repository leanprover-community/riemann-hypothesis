module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
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

theorem UpperTheory.V.Af.StrongMultiplicityOne.seed :
    UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.StrongMultiplicityOne.SeedConv → UpperTheory.V.Af.StrongMultiplicityOne.NiceOf → UpperTheory.V.Af.StrongMultiplicityOne.Seed := by
  intro hW hS hN E _ _ _ n U hU l sU
  have nice : ∀ φ ∈ U, Nice φ.1 := fun φ hφ => (hN E n φ).2 (l hφ)
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 hU
  have N := nice φ hφ
  have hg : ∃ g, whittaker φ.1 g ≠ 0 := by
    by_contra h
    refine h0 (Subtype.ext (MultiplicityOne.eq_zero_of_whittaker_eq_zero N.cont N.left N.cusp ?_
      fun g => not_not.1 fun h' => h ⟨g, h'⟩))
    rw [Fb.finEmb_eq]
    exact N.level
  obtain ⟨g, hg⟩ := hg
  rw [← GlobalTheory.CuspRep.infGL_mul_finGL g] at hg
  generalize GeneralLinearGroup.map (pInf E) g = y at hg
  generalize GeneralLinearGroup.map (pFin E) g = k at hg
  have hφ' := sU.τ k φ hφ
  refine ⟨_, hφ', hS E n _ (hW E n _ (nice _ hφ')).1 y ?_⟩
  have e : (finRepCusp E n k φ).1 = fun x => φ.1 (x * finGL E n k) := by
    rw [← Fb.finEmb_eq]
    rfl
  rw [e]
  simpa only [whittaker, mul_assoc] using hg
