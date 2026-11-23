module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ReHermitianCombinationNonpos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NegOnePowSq
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBeta

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem localSign_sq (p : PlF D) (a : Fin (D.R.rS + 1)) : TermLoc.sgnP D p a * TermLoc.sgnP D p a = 1 := by
  unfold TermLoc.sgnP
  split
  · rename_i sg _
    rw [← map_mul, Prod.mk_mul_mk, Formalism.L2.SG.Pf.FibD.neg_one_pow_sq, one_mul]
    exact map_one sg.e.symm
  · exact one_mul 1

theorem hu_all (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) :=
  IsUnit.mul ⟨Units.mkOfMulEqOne _ _ (localSign_sq p a), rfl⟩
    (Formalism.L2.SG.Pf.StabShape.frFac_unit Zd.δ Zd.M (Zd.agree p) a)

theorem frame_mem_UUE {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (G : LFlag (D.sp.Y 0) D.R.rS T') (b : Fin (D.R.rS + 1)) :
    frame G b ∈ UUE Λ F (liftF G) := by
  induction b using Fin.lastCases with
  | last =>
    rw [frame_lastG]
    apply Submodule.subset_span
    show G.fl.z ∈ (UU Λ F (liftF G) : Set (VS D).V)
    exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  | cast i =>
    rw [frame_csG]
    haveI := hΛ
    obtain ⟨s, hs, hsv⟩ := Formalism.L2.SG.Pf.exists_smul_mem Λ (G.fl.e i)
    have hX : s • G.fl.e i ∈ UU Λ F (liftF G) := by
      refine Submodule.mem_sup_left (Submodule.mem_sup_right ⟨hsv, ?_⟩)
      show s • G.fl.e i ∈ (Xsp (liftF G) : Set (VS D).V)
      exact Submodule.smul_of_tower_mem _ s (Submodule.subset_span ⟨i, rfl⟩)
    have hs' : ((s : D.host.E)) ≠ 0 := by exact_mod_cast hs
    have e : G.fl.e i = ((s : D.host.E))⁻¹ • (s • G.fl.e i) := by
      rw [← algebraMap_smul (R := 𝓞 D.host.E) D.host.E s (G.fl.e i), smul_smul]
      show G.fl.e i = (((s : D.host.E))⁻¹ * algebraMap (𝓞 D.host.E) D.host.E s) • G.fl.e i
      rw [show algebraMap (𝓞 D.host.E) D.host.E s = (s : D.host.E) from rfl, inv_mul_cancel₀ hs', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hX)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement
