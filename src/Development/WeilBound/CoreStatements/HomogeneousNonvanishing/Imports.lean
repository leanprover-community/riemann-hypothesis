module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeIntOfProjectiveRingOfIntegers
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIsometryEquivarianceStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProIsometryOfLocalIsometriesStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistedModuleFiniteProjectiveRankStatement
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H), Nonempty (TwIso D g) := by
  intro E _ _ _ H D g
  have := D.fin
  have := D.proj
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.twisted_module_finite_projective_rank (𝓞 E) g.s D.La
  have := finite_int_of_finite_ringOfIntegers E D.La
  have := finite_int_of_finite_ringOfIntegers E (TwMod g.s D.La)
  have := free_int_of_projective_ringOfIntegers E D.La
  have := free_int_of_projective_ringOfIntegers E (TwMod g.s D.La)
  refine GlobalTheory.T.pro_isometry_of_local_isometries (𝓞 E) D.La (TwMod g.s D.La) D.EF (twForm D g) fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, k1, k2⟩ := tw_g_padic E H.bar H.bar_eq H.unram p D.La (TwMod g.s D.La) D.EF (twForm D g) h3.symm D.alt
    D.unimod D.adj D.alt D.unimod fun a x y => (D.adj (g.s a) x y).trans (by rw [← g.s_bar]; rfl)
  exact GlobalTheory.T.padic_isometry_equivariance p (𝓞 E) D.La (TwMod g.s D.La) D.EF (twForm D g) φ k1 k2

end PositivityTheory.UnitarySelfGeneration
