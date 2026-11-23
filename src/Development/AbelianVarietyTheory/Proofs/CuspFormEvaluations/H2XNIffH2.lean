module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.GlobalFamilyData
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : SecNorm B) (X : PJ D B P j) (E : PtExt X)
  (hM : IntAtExt X E)

abbrev xN : PJ D n.base P j := PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (xplus X E hM)

def globalFamilyDataBaseChange {ka wL wF : WeightFamilies.Wt D j} (G : EtaleWeightGaps.GlobalFamilyData X ka wL wF) : EtaleWeightGaps.GlobalFamilyData (xN n X E hM) ka wL wF where
  N := G.N
  w := G.w
  del := G.del
  th' := G.th'
  rz := G.rz
  alz := G.alz
  th0 := G.th0
  zc := G.zc
  rq := G.rq
  th := G.th
  iet := G.iet
  et := G.et
  mx := G.mx

end General

end GlobalTheory.RunIn
