module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Mathlib.Algebra.Module.Torsion.Prod
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

def lagFrame (W : HSp D) (Y : Lag W) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  let b := Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1
  (Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a,
    Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a)

theorem lagFrame_isLagFrame (W : HSp D) (Y : Lag W) : IsLagFrame W Y (lagFrame W Y) := by
  unfold IsLagFrame lagFrame
  have h : (Set.range fun j =>
      ((fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a) a j),
        (fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a) a j))) =
      (Y.1.subtype) '' Set.range (Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.RawLift

end
