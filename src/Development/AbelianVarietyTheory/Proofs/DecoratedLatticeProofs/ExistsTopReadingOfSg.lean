module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsJ
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRho
import Formalism.LocalToGlobal.Columns.BaseLemmas
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.MainNotions.S Formalism.IndefR.Mult in
theorem GlobalTheory.SeeSaw.exists_isJ_of_par {D : D7} {u : D.what₂.Word}
    (hsg : ∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i)
    {par} (M : DSModel D.sp.X' par) (hpar : par = parB (Ptw D) D.R.m) :
    ∃ j, GlobalTheory.Core.Rk.Top.IsJ u M j := by
  subst hpar
  obtain ⟨j, hj⟩ := GlobalTheory.Core.Rk.Top.exists_isJ D u M
  exact ⟨j, hj hsg⟩

theorem GlobalTheory.SeeSaw.sg_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (i : Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (τ) :
    ((((I.rec7 l Z).fm u).sg τ).w i : ℚ) =
      sgHC (I.rec7 l Z).R ((I.rec7 l Z).hcW u τ) i - rhoVec ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) i := by
  have h2 := (TC.tup_sgHC_eq (B.hcW u τ) i).trans
    (congrArg (fun P => Formalism.L2.Col.RowPar.sgHC P i) (TC.tup_rowPar_eq B u τ))
  exact (Formalism.L2.Col.RowPar.sg_eq (B.hc τ) i).trans (congrArg (· - _) h2.symm)
