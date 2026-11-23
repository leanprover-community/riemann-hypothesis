module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGeneration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTraceLevelCompatibleProofStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRows
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
theorem traceOfAt_alt : _root_.GlobalTheory.BigOn.Exp.SerBase.TraceAt' := by
  refine _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hR hM w hw j => ?_
  intro ρ hρ hpin hlev h P
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have key := GlobalTheory.T.thetaTraceLevelCompatible_proof _ _ _ _ _ _ (R2 p) (F2 p) hC j _ (hρ.base _ j _) hBo (F2 p).P0 (F2 p).ψ0⁻¹
    ((p.R.eG.trans p.cG).trans (ρ.eG ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)))
    ?_ ?_ ?_ _ (hρ.weil_base _ j _) h P
  · exact key.symm
  · intro g Q hQ hQ' a c
    have e := hpin.grp ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) ((p.R.eG.trans p.cG) g) Q hQ hQ' a c
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at e
    exact e
  · intro g
    exact mem_level_iff hM.2.2 hlev _ j _ g
  · intro u hu
    refine (level_chi hM.2.2 hρ hlev _ j _ u hu).1.trans ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rfl
end GlobalTheory.BigOn.Exp.SerBase
end
end
