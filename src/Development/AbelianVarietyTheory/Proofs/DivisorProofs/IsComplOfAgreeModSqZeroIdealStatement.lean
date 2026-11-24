module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Ideal.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsComplOfAgreeModSqZeroIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Mathlib.RingTheory.DividedPowers.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isCompl_of_agree_mod_sqZero_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = 0 → ∀ (C : Type 1) [AddCommGroup C] [Module R C] (F K N : Submodule R C), IsCompl F N → K ⊔ I • ⊤ = F ⊔ I • ⊤ → ((K ⊓ I • ⊤ = F ⊓ I • ⊤ → IsCompl K N) ∧ ((∃ N', IsCompl K N') → K ⊓ I • ⊤ = F ⊓ I • ⊤ ∧ ∃ u : F →ₗ[R] C, (∀ c, u c ∈ I • (⊤ : Submodule R C) ∧ u c ∈ N ∧ c.1 - u c ∈ K) ∧ (∀ c : F, c.1 ∈ I • (⊤ : Submodule R C) → u c = 0) ∧ ∀ k ∈ K, ∃ c : F, k = c.1 - u c)) := by
  first | exact @GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero | exact GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero | (intros; apply GlobalTheory.SqZeroSummand.summand_of_agree_mod_sqZero <;> assumption)
