module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.MemLatWIff
public import Development.WeilBound.ThetaLifts.SmallCones.IwaGlob
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

namespace PositivityTheory.ThKCT

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem iwaEx_of (hS : StabEx) : IwaEx := by
  intro F E _ _ _ _ _ σ B n n₁ X r s H hB hX hx h0 K hK
  obtain ⟨K₀, -, -, k1, k2, -⟩ := hS F E σ B n X r s hB hX
  obtain rfl : K = K₀ := Subgroup.ext fun g => (hK g).trans (k1 g).symm
  exact ⟨k2, IwaG.iwa_glob hB hX hx h0 (fun v _ hg => PositivityTheory.ThKG.Loc.Iwa.iwaLoc hB (Or.inl hX) hx h0 v hg) hK⟩

end PositivityTheory.ThKCT

end
