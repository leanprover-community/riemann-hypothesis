module

public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
public import Formalism.SharpRestriction.SmoothDesignExistence.AdmissibleTopsMertens
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.DIV.LinkGCl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2.Top3

variable {eps : ℝ}

theorem admissible_tops_of_class {𝒜 : FamClass} {C0 : ℝ} (Fm : FamP eps) (hc : D3 C0 𝒜 Fm) : Formalism.MainNotions.G.Adm2F Fm :=
  admissible_tops_mertens Fm (topsF_of_chosenE Fm hc.2.1.choose_spec)

end Formalism.L2.DIV.LinkGCl

end
