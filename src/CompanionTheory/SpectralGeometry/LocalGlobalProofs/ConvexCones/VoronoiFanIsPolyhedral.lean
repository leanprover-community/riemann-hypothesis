module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.PsdConeFinitelyManyOrbitsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VorFunHomogSuperadd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFunctionIntegralPositiveStatement
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem vorFun_isPolyFan : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (g q : ℕ),
    (∀ (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], HasRedCover bar Y) →
    Module.finrank ℤ O * q ≤ g → IsPolyFan bar q (vorFun O g) := by
  intro O _ _ _ _ bar g q hred hg X _ _ _ _ hX
  obtain ⟨hhom, hsup⟩ := vorFun_homog_superadd O bar g X
  obtain ⟨hint, hpos⟩ := GlobalTheory.T.voronoi_function_integral_positive O bar g q X hg hX
  exact
    { homog := hhom
      superadd := hsup
      integral := fun β _ h => hint β h
      pos := fun β hβ h h0 => hpos β hβ.1 h h0
      finite := GlobalTheory.T.psd_cone_finitely_many_orbits O bar g hred X }

end GlobalTheory.CompanionTheory.Ar.Fan
