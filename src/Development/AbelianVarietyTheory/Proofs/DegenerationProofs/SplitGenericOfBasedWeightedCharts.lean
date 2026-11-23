module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSplitTorusKernelGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericInvariantsGeneratedByRatiosStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedBasePointFreeGenericFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomGenericFibreKernelTorusStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusStableWeightsGenericFibreStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Charts.split_generic_of_based : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → Charts.Split (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) c := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS a j hB
  obtain ⟨i, hi⟩ := GlobalTheory.T.exists_splitTorus_kernel_genericFibre R G C d c Sg hD hS a j hB
  obtain ⟨hst, hinv, hwt⟩ := GlobalTheory.T.torusStable_weights_genericFibre R G C d c Sg hD hS a j hB i hi
  obtain ⟨hc, hb⟩ := GlobalTheory.T.geometricallyConnected_basePointFree_generic_fibre R G C d c Sg hD hS
  exact ⟨hc, i, GlobalTheory.T.isMonHom_generic_fibre_kernel_torus R G C d c Sg hD hS a j hB i hi, hst, hinv, hwt, hb,
    GlobalTheory.T.generic_invariants_generated_by_ratios R G C d c Sg hD hS a j hB i hi hst⟩
end GlobalTheory.ZJ
