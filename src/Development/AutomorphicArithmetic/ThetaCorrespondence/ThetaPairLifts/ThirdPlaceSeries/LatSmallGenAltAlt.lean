module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeHasSmallGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGeneration
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem latSmallGen_alt : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  refine ⟨0, fun x hx _ i p hR hM w _ j ρ hρ hpin h P hP => ?_⟩
  have hL := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hio : IoExt (R2 p) := hR.ioExt
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) :=
    by
      have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
      exact { h0 with }
  exact coefLat_le_span hC ⟨fw2 p⟩ hio j (hL.2.2.2.2.2.2.1 j) _ (hρ.base _ j _) hBo (hρ.isCoefRing _ _)
    (smallInt_isCoefRing _) _ hP
end GlobalTheory.BigOn.Exp
end
end
