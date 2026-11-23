module

public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.KernelStabilizer
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.KernelStabilizer

namespace Formalism.L2.KerInert.SecondKernelStabilizers

def StabEqAny : Prop :=
  ∀ (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Fl : Fills (D.gat u w h)) (Lv : Levels Fl)
    (K : CmpJ.KerLabelsMu Tw u μ w h Lv) (I : CmpJ.CmpJIn Tw u μ w h Lv) (H : CmpJ.CmpJHyp c I) (hS : BlockRationalityField)
    (Gt : GatTies D) (Ch : Chain Lv) (hCh : _),
    StabEqRest (CmpJ.kerAtMu_any K H hS Gt Ch hCh)

def TieStabAny : Prop :=
  ∀ (D : D7) (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) [Fact (D.what₂.places.resChar w).Prime]
    (Fl : Fills (D.gat u w h)) (Lv : Levels Fl)
    (K : CmpJ.KerLabelsMu Tw u μ w h Lv) (I : CmpJ.CmpJIn Tw u μ w h Lv) (H : CmpJ.CmpJHyp c I) (hS : BlockRationalityField)
    (Gt : GatTies D) (Ch : Chain Lv) (hCh : _)
    (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _)
    (Y : Pend (sysAt Ch std vp unif eO eO_spec dG dG_spec om)),
    DV.Used D μ → OrbitPlaces.Stab0 D → ∀ j, j ≤ D.R.m → TieStabAt (Y := Y) u μ (CmpJ.kerAtMu_any K H hS Gt Ch hCh).cls j

theorem stabilizer_any_level : TieStabAny := by
  intro D c Tw u μ w h _ Fl Lv K I H hS Gt Ch hCh std vp unif eO eO_spec dG dG_spec om Y hU hS0 j hj
  exact stabilizer_all_instances D Tw c u μ w h Fl Lv Ch (CmpJ.kerAtMu_any K H hS Gt Ch hCh) std vp unif eO eO_spec dG dG_spec om Y
    hU hS0 K.stab_eq j hj

end Formalism.L2.KerInert.SecondKernelStabilizers
