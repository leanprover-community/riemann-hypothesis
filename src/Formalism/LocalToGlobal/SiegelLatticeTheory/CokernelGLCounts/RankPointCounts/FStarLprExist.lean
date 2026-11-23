module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfM
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExistA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExistB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarMinors
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GenericityConstantDoubleCosets
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

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LprEx

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem scal_rep (hrows : IsRowReps D F0 what₂) (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hP : IsPartner γ Z F'')
    (hGr : Gval (lf D F0) (repF γ) ≠ 0) :
    ∃ β, IsPair γ.lam (lf D F0) (repF γ) F'' β (gS D) ∧ s0 γ.lam (lf D F0) (repF γ) F'' β D.R.k = 1 ∧
      IsScalar γ.lam (lf D F0) (repF γ) F'' β := by
  obtain ⟨hE, γ', ⟨pr, hp1, hp2, hps, hpsc⟩, h3, h3e⟩ := hP
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGF : Gval (lf D F0) F'' ≠ 0 := hE.1.2.2
  obtain ⟨lam, mem, cls⟩ := γ
  obtain ⟨lam', mem', cls'⟩ := γ'
  obtain ⟨lp, mp, p1, p2, gp1, gp2, bp, ip⟩ := pr
  simp only [Formalism.L2.SG.Corank.Pair.pfst, Formalism.L2.SG.Corank.Pair.psnd] at hp1 hp2
  obtain ⟨rfl, hc1⟩ := hp1
  obtain ⟨rfl, hc2⟩ := hp2
  exact scal_move (hrows.1 _ mp) ⟨p1, gp1⟩ ⟨p2, gp2⟩ ⟨⟨repF _, h2⟩, hGr⟩ ⟨⟨F'', h3⟩, hGF⟩ h2e.symm h3e.symm
    ⟨bp, ip, hps, hpsc⟩

variable (Zd : LocDat D)



theorem lprExist_of (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprExist Zd u u' F0 what₂ := by
  intro hrows γ Z hC F'' hP p
  obtain ⟨w, hγ, -⟩ := hC
  have hR : IsRowLat D F0 γ.lam := hrows.1 γ.lam γ.mem
  have hF : FixedHyp D γ.lam (lf D F0) := hR.2.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGr : Gval (lf D F0) (repF γ) ≠ 0 := gval_repF γ w hγ
  have hgenR : IsGeneric γ.lam (gS D) (lf D F0) (repF γ) := by
    obtain ⟨hgen, -⟩ := hγ.1
    obtain ⟨F', ⟨h1, h1e⟩, hF'⟩ := hgen
    have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
      (h1e.trans h2e.symm)
    exact (PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u' F0 γ.lam hR ⟨F', h1⟩ ⟨repF γ, h2⟩ hrel).1 hF'
  have hE := hP.1
  obtain ⟨β, hPair, hs, hsc⟩ := scal_rep hrows γ Z F'' hP hGr
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u'
  have hG := Formalism.L2.SG.Pf.ScalarFramePf.gfacts_of γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1
    hE.2.2.2.1.1 hPair hs hsc hGr hE.1.2.2 hT hT'
  have hIo := hI D Zd γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1 hE.2.2.2.1.1 h2.2.1 hE.1.2.1 hPair
    hgenR hE.2.2.1 hs hsc hGr hE.1.2.2 hT hT' p
  have hξ := admissibility_witness_unitriangular γ.lam (lf D F0) F''
  have hG2 := gfacts_frameAct (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hG
  have hI2 := iotaEl_frameAct Zd p (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hIo
  obtain ⟨hId, hRe⟩ := Formalism.L2.SG.Pf.ScalarFramePf.identResp_lt Zd p γ.lam (frame (lf D F0)) _ (frame F'') β
    (Tu D u) (Tu D u') hG2 hI2
  exact ⟨Formalism.L2.SG.Pf.ScalarFramePf.phiP Zd p γ.lam (frame (lf D F0)) _ (frame F'') β hG2, hId, hRe.2.2.2.1,
    hRe.2.2.1, hRe.2.2.2.2⟩

theorem lprPart_of_iota (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprPart Zd u u' F0 what₂ :=
  lprPart_of' Zd (lprExist_of Zd hI)

end LprEx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
