module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvable
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), v ∉ T ∧ ∀ F₁ : IntermediateField (maximalRealSubfield E) Ω, FiniteDimensional (maximalRealSubfield E) F₁ → IsGalois (maximalRealSubfield E) F₁ → IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) → (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) → (∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := maximalRealSubfield E) A' ≤ F₁.fixingSubgroup) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g : G E Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ↔ ∀ z ∈ F₁, g z = z) ∧ ∀ z ∈ F₁, ∃ x ∈ maximalRealSubfield M, algebraMap M Ω x = z := by
  first | exact @GlobalTheory.KLift.exists_cm_lift | exact GlobalTheory.KLift.exists_cm_lift | (intros; apply GlobalTheory.KLift.exists_cm_lift <;> assumption)
