module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsEffAddNsmulDiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB

namespace GlobalTheory.Vert.Model

theorem topologicalKrullDim_gen : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Model O), topologicalKrullDim Z.gen.toScheme = Z.relDim := by
  intro O _ _ _ Z
  obtain ⟨q, H⟩ := Z.exists_isPullback_gen (FractionRing O)
  obtain ⟨d, hd, -⟩ := exists_topologicalKrullDim_fibres_eq_of_isPullback Z.str (FractionRing O)
    (IsLocalRing.ResidueField O) IsLocalRing.residue_surjective (IsPullback.of_hasPullback _ _) H
  rw [hd, relDim_eq_iff.2
    (IntModel.topologicalKrullDim_eq_succ (IsDiscreteValuationRing.not_isField O) H hd)]

end GlobalTheory.Vert.Model
