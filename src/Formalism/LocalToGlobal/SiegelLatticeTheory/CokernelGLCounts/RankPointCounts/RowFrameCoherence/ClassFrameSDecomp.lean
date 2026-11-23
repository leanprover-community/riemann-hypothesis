module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameOO3FrameValTrans
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianCombinationZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SpanPreservation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPf
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.RowForm

namespace LocalFrameDecomposition

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem frameLoc (w : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F) :
    PI.SchurPlaces.LeviLA.Frame (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR w)) (X.wfr w v) := by
  let fr := Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v
  exact
    { ee := fr.ee
      ef := fr.ef
      ff := fr.ff
      ez := fr.ez
      fz := fr.fz
      ew := fr.ew
      fw := fr.fw
      zw := fr.zw
      ww := fr.ww
      zz := fun h0 => fr.T_ne (neg_eq_zero.1 (fr.zz.symm.trans h0))
      card := by
        have h := fr.card
        omega }

end LocalFrameDecomposition

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem sDecompC_holds (w : D.what₂.Word) : SDecompC X w := by
  intro g hg
  have hgi : g⁻¹ ∈ X.SinfU w := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X w hg
  have hS : ∀ v, InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) (uMat (g⁻¹ v)) := hgi
  choose V hVu hVe hVf hVz _ hVN using fun v =>
    PI.SchurPlaces.LeviLA.levi_place (LocalFrameDecomposition.frameLoc X w v)
      ((g⁻¹ v : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) (g⁻¹ v).2 (hS v)
  let s0 : X.B.I.Ginf := fun v => ⟨V v, hVu v⟩
  have hs0 : ∀ v, uMat (s0 v) = (V v : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := fun v => rfl
  have hs0H : s0 ∈ HsetU X w := by
    intro v p hp
    rw [hs0]
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact hVe v a
    · exact hVf v a
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact hVz v
  have hN : s0⁻¹ * g⁻¹ ∈ X.NinfU w := fun v => by
    have e : uMat ((s0⁻¹ * g⁻¹) v) =
        (((V v)⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
          uMat (g⁻¹ v) := rfl
    rw [e]
    exact hVN v
  have hN' := Formalism.L2.SG.RealObj.SpanPreservation.ninfU_inv X w hN
  rw [_root_.mul_inv_rev, inv_inv, inv_inv] at hN'
  exact ⟨g * s0, hN', s0⁻¹, Formalism.L2.SG.RealObj.InfCut.hsetU_inv X w hs0H, by group⟩

end Formalism.L2.SG.Pf.RowForm
