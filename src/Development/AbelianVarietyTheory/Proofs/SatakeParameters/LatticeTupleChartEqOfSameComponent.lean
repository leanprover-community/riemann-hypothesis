module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc



theorem chart_eq_of_comp : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), ((sysS H X std).Pj j).IsLatTup La → ((sysS H X std).Pj j).IsLatTup Lb → J.chart std j hj (c, La) = J.chart std j hj (c, Lb)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _ j hj c La Lb hLa hLb
  unfold Joint.chart
  rcases j with _ | j
  · haveI := J.ch0
    exact Subsingleton.elim _ _
  · simp only
    rw [Formalism.MainNotions.G.KAat.clsAt_succ X H j hj c La, Formalism.MainNotions.G.KAat.clsAt_succ X H j hj c Lb]
    have ea := Formalism.MainNotions.G.KAat.clsOf_chart (S := (I.at' j hj).st) (H.core j hj) c La hLa
    have eb := Formalism.MainNotions.G.KAat.clsOf_chart (S := (I.at' j hj).st) (H.core j hj) c Lb hLb
    have key : ∀ (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (h : (I.at' j hj).C = C) (St' : GlobalTheory.TwU.StepCharts C (j + 1) hj)
        (_ : St' = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st)) (x y : (I.at' j hj).C.cls (j + 1)),
        (I.at' j hj).st.chOf x = (I.at' j hj).st.chOf y →
        St'.chOf (Formalism.MainNotions.G.KAat.castCls h (j + 1) x) = St'.chOf (Formalism.MainNotions.G.KAat.castCls h (j + 1) y) := by
      intro C h St' hst x y e
      subst h
      subst hst
      exact e
    exact key _ (X.onCh j hj) _ (J.st j hj) _ _ (ea.trans eb.symm)

end GlobalTheory.TwV.Xc
