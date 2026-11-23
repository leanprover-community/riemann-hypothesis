module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsGrid
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Batteries.Logic
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsChain
public import Development.AutomorphicArithmetic.LocalEmbeddings.JetsGlue

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section
open GlobalTheory.DefStep GlobalTheory.JetsOne GlobalTheory.ExpansionInvariance

private theorem pair_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (c : ℂ) (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0)))
    (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) (X : ∀ j, FinPt G (.top j))
    (Y : ∀ i, FinPt G (.grid i D.R.m)) :
    c * pairPts S τ X Y (Ψ (X 0)) (F (Y 0)) = τ.sum fun d a => a *
      GlobalTheory.JetsOne.pairP (V := fun j => G.V (.top j)) (V' := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.top j)))
        (Mo' := fun j => VV ℂ (wt G (.grid j D.R.m))) (colComp S d) (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x))
        (rowComp S d) (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹
          (funOf (listedWt G (.grid 0 D.R.m)) (F x))) D.R.m
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) X Y := by
  rw [pairPts, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine (mul_left_comm c (τ d) _).trans (congrArg (τ d * ·) ?_)
  exact (congrArg₂ (fun a b => (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) a b)
    (ptV_eq_chainTo (V := fun j => G.V (.top j)) (Mo := fun j => VV ℂ (wt G (.top j))) (colComp S d)
      (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x)) X D.R.m)
    (ptV_eq_chainTo (V := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.grid j D.R.m))) (rowComp S d)
      (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) (F x)))
      Y D.R.m)).symm

end
