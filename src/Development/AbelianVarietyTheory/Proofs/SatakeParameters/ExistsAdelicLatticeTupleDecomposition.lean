module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem dec_exists : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → Nonempty (Dec J std)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  classical
  refine ⟨{ gam := fun j hj La => if h : ((sysS H X std).Pj j).IsLatTup La.2 then Classical.choose (hD j hj La h).2.1 else 1,
            kap := fun j hj La => if h : ((sysS H X std).Pj j).IsLatTup La.2 then
              Classical.choose (Classical.choose_spec (hD j hj La h).2.1).2 else 1,
            mem := ?_, eq := ?_ }⟩
  · intro j hj La
    by_cases h : ((sysS H X std).Pj j).IsLatTup La.2
    · rw [dif_pos h]
      exact (Classical.choose_spec (hD j hj La h).2.1).1
    · rw [dite_eq_right h]
      exact Subgroup.one_mem _
  · intro j hj La h
    simp only [dif_pos h]
    exact Classical.choose_spec (Classical.choose_spec (hD j hj La h).2.1).2

end GlobalTheory.TwV.DelB
