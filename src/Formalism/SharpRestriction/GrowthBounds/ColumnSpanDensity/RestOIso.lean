module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LpRingIndepOf
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.QuadraticBasis.FinalO
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

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem restOIso : RestOIso := fun p n' R₁ R₂ φW =>
  QuadraticBasis.oIso p n' R₁.std.1.prime (by have := R₁.std.1.two_le; omega) R₁.W R₂.W R₁.O R₂.O R₁.jO R₂.jO R₁.w R₂.w
    R₁.std.1.p_unif R₂.std.1.p_unif R₁.std.1.res_card R₂.std.1.res_card R₁.std.1.eq_sum_herm_smul_frame_of_inW R₂.std.1.eq_sum_herm_smul_frame_of_inW
    R₁.std.1.finite R₂.std.1.finite R₁.std.1.complete_O R₂.std.1.complete_O R₁.std.1.w_sq R₂.std.1.w_sq
    R₁.std.2.1 R₂.std.2.1 R₁.std.2.2.1 R₂.std.2.2.1 φW

end Formalism.MainNotions.flipOneThree.Pf
