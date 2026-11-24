module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummandDualAnnihilatorReductionProjective
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

theorem _root_.GlobalTheory.T.summand_dualAnnihilator_reduction_projective : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (C C₀ : Type 1) [AddCommGroup C] [Module R C] [AddCommGroup C₀] [Module R₀ C₀], Module.Finite R C → Module.Projective R C → ∀ ρ : C →ₛₗ[π] C₀, Function.Surjective ρ → (∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C)) → ∀ F₀ : Submodule R₀ C₀, (∃ N₀, IsCompl F₀ N₀) → (∀ K : Submodule R C, (∃ N, IsCompl K N) → (∃ N, IsCompl K.dualAnnihilator N) ∧ K.dualAnnihilator.dualCoannihilator = K ∧ ((∀ c, c ∈ K ⊔ RingHom.ker π • ⊤ ↔ ρ c ∈ F₀) ↔ ∀ y : Module.Dual R₀ C₀, y ∈ F₀.dualAnnihilator ↔ ∃ x ∈ K.dualAnnihilator, ∀ c, y (ρ c) = π (x c))) ∧ ∀ G : Submodule R (Module.Dual R C), (∃ N, IsCompl G N) → ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  first | exact @GlobalTheory.LiftSys.summand_dual_reduction | exact GlobalTheory.LiftSys.summand_dual_reduction | (intros; apply GlobalTheory.LiftSys.summand_dual_reduction <;> assumption)
