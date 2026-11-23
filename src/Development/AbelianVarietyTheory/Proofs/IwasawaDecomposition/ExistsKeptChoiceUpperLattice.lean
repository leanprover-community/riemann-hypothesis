module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtSame
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove


theorem tupTied_ext {D : D7} {cf : CharFrame D} {C : NChoice D} {p q : TupTied D cf C} (h1 : p.xi = q.xi) (h2 : p.psi = q.psi) :
    p = q := by
  cases p; cases q; cases h1; cases h2; rfl

section
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) {nch : NChoice (w.D Z)}
  {xd : ThData (w.D Z)}

theorem nchT_up (n : NchT w Z Wt nch) : Nonempty (NchT w (upL Z S' N h) Wt (nchUp S' N h nch)) :=
  ⟨{ tp := {
       xi := by with_unfolding_all exact (n.tp.xi :)
       xi_inj := by with_unfolding_all exact (n.tp.xi_inj :)
       xi_fin := by with_unfolding_all exact (n.tp.xi_fin :)
       xi_triv := by with_unfolding_all exact (n.tp.xi_triv :)
       xi_tame := by with_unfolding_all exact (n.tp.xi_tame :)
       psi := by with_unfolding_all exact (n.tp.psi :)
       trueColumnChoices_heckeChar_reference_eq_one := by with_unfolding_all exact (n.tp.trueColumnChoices_heckeChar_reference_eq_one :)
       xi_star := by with_unfolding_all exact (n.tp.xi_star :)
       xi_star' := by with_unfolding_all exact (n.tp.xi_star' :)
       xi_tw := by with_unfolding_all exact (n.tp.xi_tw :)
       psi_is := by with_unfolding_all exact (n.tp.psi_is :)
       psi_un := by with_unfolding_all exact (n.tp.psi_un :) }
     xi := by with_unfolding_all exact (n.xi :)
     psi := by with_unfolding_all exact (n.psi :)
     tie := {
       twOf_eq := by with_unfolding_all exact (n.tie.twOf_eq :)
       twSide_eq := by with_unfolding_all exact (n.tie.twSide_eq :)
       Q_eq := by with_unfolding_all exact (n.tie.Q_eq :)
       psi_eq := by with_unfolding_all exact (n.tie.psi_eq :)
       embedding_baseField_condition := by with_unfolding_all exact (n.tie.embedding_baseField_condition :) }
     Q := n.Q
     chrPsi := by with_unfolding_all exact (n.chrPsi :) }⟩

theorem kept_up (nch : NChoice (w.D Z)) : Kept nch (nchUp S' N h nch) := by
  refine ⟨?_, ?_, ?_, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩ <;> constructor <;> rfl

theorem goodO_up (g : GoodO (w.D Z) nch xd) : GoodO (w.D (upL Z S' N h)) (nchUp S' N h nch) (xdUp S' N h xd) := by
  dsimp only [nchUp, xdUp, upL]
  -- Abstract the new division stage before comparing the twisting conditions.
  generalize (Db.setDivZ Z N h).V = V'
  obtain ⟨⟨E, N0, S⟩, hE, hAt, hCl⟩ := g.tw
  cases hE
  refine ⟨⟨⟨twEOf _, N0, S⟩, rfl, ?_, ?_⟩, g.sep⟩
  · with_unfolding_all exact hAt
  · with_unfolding_all exact hCl
end

end GlobalTheory.LayerMove
end
