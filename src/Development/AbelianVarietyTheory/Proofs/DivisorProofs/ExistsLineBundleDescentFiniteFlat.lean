module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumFrameCocycleUnitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfDescentInvariantFramesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleTrivialNearFibreFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatUnitCocycleLocallyCoboundaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFrameInvariantUnderDescentDatumStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBDescent

theorem exists_descent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (L : LB X), L.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, GlobalTheory.LBDescent.chart f L i j)ˣ), GlobalTheory.LBDescent.DescCompat f L φ → GlobalTheory.LBDescent.DescCocycle f L φ → ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  intro X Y f _ _ _ _ L hL φ hc hcoc
  refine GlobalTheory.T.exists_lineBundle_of_descentInvariant_frames f L hL φ fun y => ?_
  obtain ⟨V, hy, t, ht⟩ := GlobalTheory.T.exists_lineBundle_trivial_near_fibre_finite f L hL y
  obtain ⟨c, hct, hcc⟩ := GlobalTheory.T.descentDatum_frame_cocycle_unit f L hL φ hc hcoc V t ht
  obtain ⟨V', hle, hy', u, hu⟩ := GlobalTheory.T.finiteFlat_unitCocycle_locally_coboundary f V c hcc y hy
  exact ⟨V', hy', GlobalTheory.T.twisted_frame_invariant_under_descentDatum f L φ V t ht c hct V' hle u hu⟩

end GlobalTheory.LBDescent
