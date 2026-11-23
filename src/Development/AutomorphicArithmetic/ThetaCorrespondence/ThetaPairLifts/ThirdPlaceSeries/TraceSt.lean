module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGeneration
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
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.ConjTwist (BaseOf)


attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TraceFlatLevel
open GlobalTheory.TraceLevelPf
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end GlobalTheory.TraceFlatLevel
namespace GlobalTheory.BigOn.Exp.TupLe
theorem traceSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.TraceCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm ρ hρ hpin hlev i b ψ ω hψ hQ hω h P
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B i j b) := { baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin i j b with }
  refine GlobalTheory.TraceFlatLevel.traceLevel_flat (R2 p) j (ρ.B i j b) (hρ.base i j b) hBo (F2 p).P0 (F2 p).ψ0⁻¹
    ((p.R.eG.trans p.cG).trans (ρ.eG i j b)) (fun g P h h' a c => ?_) (fun g => mem_level_iff hm.2.2 hlev i j b g)
    (fun u hu => ?_) ψ hψ hQ ω hω h P
  · have e1 := hpin.grp i j b (p.cG (p.R.eG g)) P h h' a c
    rw [MulEquiv.symm_apply_apply] at e1
    exact e1
  · refine (level_chi hm.2.2 hρ hlev i j b u hu).1.trans ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rfl
end GlobalTheory.BigOn.Exp.TupLe
end
end
