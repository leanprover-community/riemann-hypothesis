module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfShUnit
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

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

theorem shUnit_holds (D : Formalism.BasicNotions.D7) : ShUnit D := by
  intro p c
  haveI : CharZero (D.s.atP p).Fp := (D.s.atP p).char0
  haveI : Module.Free (D.s.atP p).Fp (D.s.atP p).Ep := (D.s.atP p).free
  haveI : FiniteDimensional (D.s.atP p).Fp (D.s.atP p).Ep :=
    Module.finite_of_finrank_pos (by rw [(D.s.atP p).rank]; norm_num)
  by_contra hcon
  simp only [not_exists] at hcon
  let f : Module.End (D.s.atP p).Fp (D.s.atP p).Ep := LinearMap.mulLeft (D.s.atP p).Fp c
  have hev : ∀ n : Fin 3, ∃ y : (D.s.atP p).Ep, f.HasEigenvector (-(((n : ℕ) : (D.s.atP p).Fp))) y := by
    intro n
    have hnu := hcon n
    have hni : ¬ Function.Injective
        (LinearMap.mulLeft (D.s.atP p).Fp (c + (((n : ℕ)) : (D.s.atP p).Ep))) := by
      intro hinj
      obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) 1
      exact hnu (isUnit_iff_exists_inv.2 ⟨y, hy⟩)
    rw [← LinearMap.ker_eq_bot, ← ne_eq, Submodule.ne_bot_iff] at hni
    obtain ⟨y, hyk, hy0⟩ := hni
    refine ⟨y, ?_, hy0⟩
    rw [Module.End.mem_eigenspace_iff]
    have h1 : (c + (((n : ℕ)) : (D.s.atP p).Ep)) * y = 0 := hyk
    rw [add_mul] at h1
    show c * y = _
    rw [eq_neg_of_add_eq_zero_left h1, neg_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  choose y hy using hev
  have hinj : Function.Injective (fun n : Fin 3 => -(((n : ℕ) : (D.s.atP p).Fp))) := fun a b h => by
    have h' : ((a : ℕ) : (D.s.atP p).Fp) = ((b : ℕ) : (D.s.atP p).Fp) := neg_inj.1 h
    exact Fin.ext (Nat.cast_injective h')
  have hli := Module.End.eigenvectors_linearIndependent' f _ hinj y hy
  have hc := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, (D.s.atP p).rank] at hc
  omega

theorem partnerCount_of_integral {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D) (hI : IntGenP Zd)
    (hB : BridgeBA) : PartnerIsomorphismCount Zd :=
  partnerCount_of_shUnit Zd hT2 hI (shUnit_holds D) hB

end Formalism.L2.SG.Pf.PCount
