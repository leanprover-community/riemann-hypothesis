module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohLp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfC
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfE
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfH
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfG

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem starExists2_of_good (hP : CtxP u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_parts Zd u u' F0 what₂ hP (cohGen_of Zd (cohInt_holds Zd) (cohDG_holds Zd) hGood)
    (cohIota_holds Zd) hGood

theorem starExists2_holds (hP : CtxP u u' F0 what₂) : StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_good Zd u u' F0 what₂ hP (cohGood_of Zd globGramNe_holds)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
