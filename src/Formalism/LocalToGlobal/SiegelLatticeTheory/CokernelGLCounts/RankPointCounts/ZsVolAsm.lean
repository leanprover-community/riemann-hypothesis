module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolAct
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.DiagMulOfBt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.PtMatIsUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FibMp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FibMpr
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBCongruence

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolAsm

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolAct Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem fibreIndex_holds : FibreCZ M δ u u' F0 what₂ := by
  intro γ w F' L U hH a₁ b₁ ν₁ m₁ F₁ a₂ b₂ ν₂ m₂ F₂ x₁ x₂ hx₁ hx₂ hd₁ hd₂
  obtain ⟨hA, hT, hR, hP, hE, hN⟩ := hH
  obtain ⟨hRep, hAdm, hL, hU, hZo⟩ := hN
  have hΛ : IsRowLat D F0 γ.lam := hR.1 γ.lam γ.mem
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hP.1.ne_zero
  have hZu : IsUnit (Zhat F0 F'.fl).det := by
    have hZ1 : Zhat F0 F'.fl * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS = L * ptMat w * U := by
      rw [← Formalism.L2.SG.Pf.StabilizerIndexVolumes.zhatOM_eq]; exact hZo
    have hZe : Zhat F0 F'.fl = L * ptMat w * U * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS := by
      rw [← hZ1, Matrix.mul_assoc, Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM_sq, Matrix.mul_one]
    rw [isUnit_iff_ne_zero, hZe, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Formalism.L2.SG.Pf.StabilizerIndexVolumes.lo_det hL,
      Formalism.L2.SG.Pf.StabilizerIndexVolumes.up_det hU, one_mul, mul_one]
    refine mul_ne_zero (Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det w) ?_
    intro h0
    have := congrArg Matrix.det (Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM_sq (K := D.host.E) (r := D.R.rS))
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hG₁ : Gval (lf D F0) F' ≠ 0 := by
    obtain ⟨Fa, ⟨pa, ea⟩, hGa, -⟩ := hE.2
    obtain ⟨p₁, e₁⟩ := hRep
    have hdca := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hΛ ⟨Fa, pa⟩ ⟨F', p₁⟩).1 (ea.trans e₁.symm)
    rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdca]
    exact hGa
  have hGr := Formalism.L2.SG.Pf.StabilizerIndexVolumes.gram_gg_unit F0 F'.fl (star_natCast _) (star_natCast _) hZu hG₁
  exact ⟨Formalism.L2.SG.Pf.ZsVolFib.fib_mp u u' F0 what₂ γ F' L hL hGr hZu a₁ b₁ ν₁ m₁ F₁ a₂ b₂ ν₂ m₂ F₂ x₁ x₂ hx₁ hx₂
      hd₁ hd₂,
    Formalism.L2.SG.Pf.ZsVolFib.fib_mpr u u' F0 what₂ γ F' L hL hT0 hZu a₁ b₁ ν₁ m₁ F₁ a₂ b₂ ν₂ m₂ F₂ x₁ x₂ hx₁ hx₂
      hd₁ hd₂⟩

end Formalism.L2.SG.Pf.ZsVolAsm

end
