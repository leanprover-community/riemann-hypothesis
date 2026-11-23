module

public import Formalism.LocalToGlobal.LatticeGeometry.NormDetInf
public import Formalism.LocalToGlobal.LatticeGeometry.ArVolEqOfNef
public import Formalism.LocalToGlobal.LatticeGeometry.AmpleOnAbelianBase
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Geo

structure ShimU (D : D7) (G : DV.Geo D.what₂.LL) {Lev : Type}
    (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)) (ng : NgPkg) (w : Dat D Lev) where

  Comp : Type
  [compFin : Fintype Comp]
  [compNe : Nonempty Comp]

  cx : CxPkg D.what₂.Tau w.N w.j Comp

  alg : AlgPkg G D.what₂.Tau w.N Comp

  pad : PadPkg D w.N w.j Comp jC ng

attribute [instance] ShimU.compFin ShimU.compNe

end Formalism.L2.Geo
