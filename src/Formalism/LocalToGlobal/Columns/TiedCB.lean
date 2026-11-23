module

public import Formalism.LocalToGlobal.Columns.TiedCG
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def crdN (D : ColRec) (i : ℕ) (hi : i ≤ D.R.m) : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) :=
  (D.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)

def crdP (D : ColRec) : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)


end Formalism.L2.Col.CF

end
