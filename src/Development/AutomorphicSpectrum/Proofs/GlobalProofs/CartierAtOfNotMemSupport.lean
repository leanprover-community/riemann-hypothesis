module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

theorem cartAt_of_notMem_support {X : Scheme.{0}} (J : X.IdealSheafData) (x : X) (hx : x ∉ J.support) :
    CartAt J x := by
  rw [Scheme.IdealSheafData.mem_support_iff] at hx
  push_neg at hx
  obtain ⟨U, hU⟩ := hx
  rw [Scheme.mem_zeroLocus_iff] at hU
  push_neg at hU
  obtain ⟨f, hf, hxf⟩ := hU
  refine ⟨X.affineBasicOpen f, 1, hxf, Submonoid.one_mem _, ?_⟩
  rw [Ideal.span_singleton_one, ← J.map_ideal_basicOpen U f]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
    (X.toRingedSpace.isUnit_res_basicOpen f)

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
