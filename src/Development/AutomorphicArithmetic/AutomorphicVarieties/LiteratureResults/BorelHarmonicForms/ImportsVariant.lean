module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IndepAbs
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.indep :
    UpperTheory.V.Lit.Bor.Indep := by
  intro E _ _ _ a d q s π hπ ω h0 hV c hc
  have hind : iSupIndep fun i => (π i).V :=
    UpperTheory.V.Lit.Bor.indepAbs _ (Sm E a) (fun o => act o) s (fun i => (π i).V) (fun i o x hx => (π i).stable o x hx)
      (fun i N hN hst => (π i).irred N hN hst) (fun i j hij h => hij (hπ i j h))
  have key : ∀ (X : Fin q → Herm E a) (k : Fin d) (i : Fin s), c i • cmp k (ω i X) = 0 := by
    intro X k i
    have h : ∀ (t : Finset (Fin s)) (f : Fin s → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin d → ℂ))),
        (∑ j ∈ t, f j) X = ∑ j ∈ t, f j X := fun t f => by
      induction t using Finset.cons_induction with
      | empty => rfl
      | cons j t hj ih => rw [Finset.sum_cons, Finset.sum_cons, add_apply, ih]
    have h1 : ∑ j, c j • cmp k (ω j X) = 0 := by
      have h2 := congrArg (fun η => cmp k (η X)) hc

      simpa only [h, map_sum, smul_apply, map_smul, zero_apply, map_zero] using h2
    exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind Finset.univ (fun j => c j • cmp k (ω j X))
      (fun j _ => Submodule.smul_mem _ _ (mem_tens.1 (hV j X) k)) h1 i (Finset.mem_univ i)
  funext i
  by_contra hci
  refine h0 i (AlternatingMap.ext fun X => ?_)
  rw [← sum_cmp (ω i X), zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [(smul_eq_zero.1 (key X k i)).resolve_left hci, TensorProduct.zero_tmul]
