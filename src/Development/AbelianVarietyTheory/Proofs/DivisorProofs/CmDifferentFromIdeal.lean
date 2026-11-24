module

public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.FlatCore.CMDiff

theorem latRank_iSup {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] (N : ι → Submodule (𝓞 K) V)
    (hi : iSupIndep fun i => Submodule.span K (N i : Set V)) :
    latRank K (⨆ i, N i) = ∑ i, latRank K (N i) := by
  classical
  have hs : Submodule.span K ((⨆ i, N i : Submodule (𝓞 K) V) : Set V) = ⨆ i, Submodule.span K (N i : Set V) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (iSup_le fun i => Submodule.span_mono ?_)
    · have : (⨆ i, N i) ≤ (⨆ i, Submodule.span K (N i : Set V)).restrictScalars (𝓞 K) :=
        iSup_le fun i => fun x hx => (le_iSup (fun i => Submodule.span K (N i : Set V)) i)
          (Submodule.subset_span hx)
      exact this
    · exact SetLike.coe_mono (le_iSup N i)
  unfold latRank
  rw [hs]
  have hinj : Function.Injective (DirectSum.coeLinearMap fun i => Submodule.span K (N i : Set V)) := by
    first
    | exact hi.dfinsupp_lsum_injective
    | exact (iSupIndep_iff_dfinsupp_lsum_injective _).1 hi
    | exact DirectSum.coeLinearMap_injective_of_iSupIndep hi
  rw [← DirectSum.range_coeLinearMap, LinearMap.finrank_range_of_inj hinj, Module.finrank_directSum]

end GlobalTheory.FlatCore.CMDiff

namespace GlobalTheory.FlatCore.CMDiff

end GlobalTheory.FlatCore.CMDiff

end
