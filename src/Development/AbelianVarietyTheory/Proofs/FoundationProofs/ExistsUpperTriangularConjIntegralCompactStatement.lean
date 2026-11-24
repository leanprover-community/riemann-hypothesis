module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUpperTriangularConjIntegralCompact
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_upperTriangular_conj_integral_compact : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (E : IntermediateField ℚ_[l] (Qbar l)) (r : Γ →* GL (Fin 2) (Qbar l)), FiniteDimensional ℚ_[l] E → Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ E) → ∃ B : GL (Fin 2) (Qbar l), (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0 ∧ ∀ g i j, ((B * r g * B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ E ∧ ‖((B * r g * B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) i j‖ ≤ 1 := by
  first | exact @GlobalTheory.StableLatticeTriangular.exists_upperTriangular_conj_integral | exact GlobalTheory.StableLatticeTriangular.exists_upperTriangular_conj_integral | (intros; apply GlobalTheory.StableLatticeTriangular.exists_upperTriangular_conj_integral <;> assumption)
