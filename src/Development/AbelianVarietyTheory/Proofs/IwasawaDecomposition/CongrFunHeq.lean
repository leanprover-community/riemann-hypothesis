module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtSame
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedRowLoc
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D)

def Mv.lam (x : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat m.D := @_root_.GlobalTheory.LamTie.LamDat.mk (_)
    (C := @_root_.Formalism.L2.Host.CharFrame.mk (_)
      (P := (by with_unfolding_all exact (x.C.P :)))
      (W := (by with_unfolding_all exact (x.C.W :)))
      (mu0 := (by with_unfolding_all exact (x.C.mu0 :)))
      (eta := (by with_unfolding_all exact (x.C.eta :)))
      (chiPsi := (by with_unfolding_all exact (x.C.chiPsi :)))
      (del := (by with_unfolding_all exact (x.C.del :)))
      (del' := (by with_unfolding_all exact (x.C.del' :)))
      (isMu0 := (by with_unfolding_all exact (x.C.isMu0 :)))
      (isEta := (by with_unfolding_all exact (x.C.isEta :)))
      (isChi := (by with_unfolding_all exact (x.C.isChi :)))
      (isDel := (by with_unfolding_all exact (x.C.isDel :)))
      (isDel' := (by with_unfolding_all exact (x.C.isDel' :))))
    (q0 := (by with_unfolding_all exact (x.q0 :)))
    (w0 := (by with_unfolding_all exact (x.w0 :)))
    (c := (by with_unfolding_all exact (x.c :)))
    (chi := (by with_unfolding_all exact (x.chi :)))
theorem Mv.lam_ok {l : GlobalTheory.LamTie.LamDat D} (x : l.Ok) : (m.lam l).Ok := @_root_.GlobalTheory.LamTie.LamDat.Ok.mk (_) (_)
    (places := (by with_unfolding_all exact (x.places :)))
    (aux := (by with_unfolding_all exact (x.aux :)))
    (big := (by with_unfolding_all exact (x.big :)))
theorem Mv.lam_teich {l : GlobalTheory.LamTie.LamDat D} (x : l.Teich) : (m.lam l).Teich := (by with_unfolding_all exact (x :))
theorem Mv.lam_tie {l : GlobalTheory.LamTie.LamDat D} (x : GlobalTheory.LamTie.IsLamTieFull D.ntw l) : GlobalTheory.LamTie.IsLamTieFull m.D.ntw (m.lam l) := (by with_unfolding_all exact (x :))

theorem Mv.rowLoc {D : D7} (m : Mv D) {C : NChoice D} (a : NAllC D C) (F : Formalism.L2.RowFrame D) (F' : Formalism.L2.RowFrame m.D)
    (hF : HEq F'.rep F.rep) (x : Formalism.L2.RowLocTied D a.gal.lp F) : Formalism.L2.RowLocTied m.D (m.all a).gal.lp F' := by
  obtain ⟨rep, inj⟩ := F
  obtain ⟨rep', inj'⟩ := F'
  have e : rep' = (by with_unfolding_all exact (rep :)) := eq_of_heq ((by with_unfolding_all exact (hF :)))
  subst e
  exact (@_root_.Formalism.L2.RowLocTied.mk (_) (_) (_)
    (sat := (by with_unfolding_all exact (x.sat :)))
    )

theorem congrFun_heq {α β : Type} {f g : α → β} (h : HEq f g) (x : α) : f x = g x := by rw [eq_of_heq h]

end GlobalTheory.LayerMove
end
