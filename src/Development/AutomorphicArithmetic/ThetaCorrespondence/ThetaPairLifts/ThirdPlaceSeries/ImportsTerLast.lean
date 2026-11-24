module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRecPins
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.RecPinsTie
theorem main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S), ∀ r : _root_.GlobalTheory.Mem.R3.RecursiveInput y, (∀ hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y), _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt Rc.T.n.gal.lp x.R.θ x.Y.PY (x.R.MY 0) (fun b => levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun b => Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 b))) (fun _ => x.R.e0) x.Y.eFT → _root_.Formalism.IndefR.IndefiniteRealisationCompatible hp (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r)) ∧ (Formalism.IndefR.RecTie.PartsRec x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.PY x.Y.PW x.Y.eFT r.E r.labPi r.piOf x.Y.Ish.prt x.Y.IL.prtW → (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r).PartsRow) ∧ PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG := by
  intro D L hT Gi Gl K Yd cX ex x Rc S y r
  refine ⟨fun hp h => ⟨?_, ?_⟩, fun h => ?_, ?_⟩
  · exact x.Y.stdPsi
  · exact h
  · exact h
  · exact x.pins.keep.psi
end GlobalTheory.Mem.R3.RecPinsTie
end
