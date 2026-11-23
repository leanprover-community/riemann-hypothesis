module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideB
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



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove

variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.choiceSide_alt {low Pq S hk eig θ} {Bs : SideB D cf A.row low Pq S hk eig θ} (x : ChoiceSide D cf M Bs.exp C tp) : ChoiceSide m.D (m.cf cf) (m.mt M) (m.sideB_alt Bs).exp (m.ch C) (m.tp tp) := @_root_.GlobalTheory.HeightCounting.ChoiceSide.mk (_) (_) (_) (_) (_) (_)
    (nct := @_root_.Formalism.BasicNotions.NChTie.mk (_) (_)
      (twOf_eq := (by with_unfolding_all exact (x.nct.twOf_eq :)))
      (twSide_eq := (by with_unfolding_all exact (x.nct.twSide_eq :)))
      (Q_eq := (by with_unfolding_all exact (x.nct.Q_eq :)))
      (psi_eq := (by with_unfolding_all exact (x.nct.psi_eq :)))
      (embedding_baseField_condition := (by with_unfolding_all exact (x.nct.embedding_baseField_condition :))))
    (choice := @_root_.GlobalTheory.HeightCounting.ChoiceC.mk (_) (_)
      (twI_conj := (by with_unfolding_all exact (x.choice.twI_conj :)))
      (sd_place := (by with_unfolding_all exact (x.choice.sd_place :)))
      (emb_side := (by with_unfolding_all exact (x.choice.emb_side :)))
      (sd_conj := (by with_unfolding_all exact (x.choice.sd_conj :)))
      (one := (by with_unfolding_all exact (x.choice.one :)))
      (conj := (by with_unfolding_all exact (x.choice.conj :))))
    (off := (by with_unfolding_all exact (x.off :)))
    (adm := (by with_unfolding_all exact (x.adm :)))
    (psi := (by with_unfolding_all exact (x.psi :)))
    (eMt_level := (by with_unfolding_all exact (x.eMt_level :)))
end
section
end
end GlobalTheory.LayerMove
end
end
