module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecayStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EZeroThetaDescentEval
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GoodFix
open Formalism.L2.DIV
end GlobalTheory.GoodFix
namespace GlobalTheory.GoodFix
open Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev
end GlobalTheory.GoodFix
namespace GlobalTheory.GoodFix
end GlobalTheory.GoodFix
open GlobalTheory.GoodFix in

theorem GlobalTheory.GoodFix.e_zero_theta_descent_eval_alt_bis : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ t (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) (v : ((_root_.GlobalTheory.Fam.pk_z W).MY 0).Vec), (_root_.GlobalTheory.Fam.pk_z W).e0 ((_root_.GlobalTheory.Fam.pk_z W).thDn t ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) (PiTensorProduct.tprod ℂ v)) = (_root_.GlobalTheory.Fam.pk_z W).thDn t ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)) (PiTensorProduct.tprod ℂ v) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP t F v
  have hC := hP.bot.hyp.2.2.2.1
  have hL := hP.lev
  unfold _root_.GlobalTheory.MiS.LevelHypothesis at hL
  obtain ⟨⟨s, hs⟩, -⟩ := hL
  have hgf := good_fix (W.P.A3.A.fam.R t) (W.P.A3.A.fam.lvl W.Q.F.P1 W.Q.F.ψ1) hs.ok2.irr F
  exact goodProjector_fixes_compositeThetaLift_of_fixed GlobalTheory.T.cusp_forms_rapid_decay (_root_.GlobalTheory.Fam.pk_z W) hC.lev hC.models hC.chain hC.grp.red_R t _ hgf v
end
