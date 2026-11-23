module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContinuousCocycleMapApply
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

open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.selBase :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (O M' : Type) [CommRing O] [Algebra R O] [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)] [Module.Free R O]
      [Module.Finite R O] [AddCommGroup M'] [Module O M'] [Module R M'] [IsScalarTower R O M'] [TopologicalSpace M']
      [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M'] (ρ' : Representation O G M') (j : M →ₗ[R] M'),
      IsBaseChange O j → (∀ g m, j (ρ g m) = ρ' g (j m)) → ∀ (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O (LocSel ρ' U 𝒟) = Module.length R (LocSel ρ U 𝒟) * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ O M' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' j hb hj U 𝒟
  exact length_of_isBaseChange (isBaseChange_selMap ρ ρ' j hj U hb 𝒟)
