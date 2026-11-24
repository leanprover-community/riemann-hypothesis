module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

theorem _root_.GlobalTheory.T.padicHodgeProperties_conj_invariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r r' : ↥Gw →* GL (Fin a) (Om l)) (A : GL (Fin a) (Om l)), (∀ g, r' g = A * r g * A⁻¹) → (IsdRAt P Bw r → IsdRAt P Bw r') ∧ (IsCrysAt P Bw r → IsCrysAt P Bw r') ∧ (IsPotCrysAt P Bw r → IsPotCrysAt P Bw r') ∧ ∀ (τ : E →+* Om l) (J : Multiset ℤ), IsJumpsAt P Bw r τ J → IsJumpsAt P Bw r' τ J := by
  first | exact @GlobalTheory.ConjLocal.local_conj | exact GlobalTheory.ConjLocal.local_conj | (intros; apply GlobalTheory.ConjLocal.local_conj <;> assumption)
