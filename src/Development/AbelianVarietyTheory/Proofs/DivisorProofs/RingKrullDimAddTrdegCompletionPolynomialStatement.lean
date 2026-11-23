module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimAddTrdegCompletionPolynomial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.ringKrullDim_add_trdeg_completion_polynomial : ∀ (F W R : Type) [Field F] [CommRing W] [IsDomain W] [IsLocalRing W] [CommRing R] [IsLocalRing R] (b : F →+* W), b.EssFiniteType → ∀ (I : Type) [Fintype I] (ψ : MvPolynomial I W →+* R), GlobalTheory.TChart.IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) → ∀ bR : F →+* R, (ψ.comp MvPolynomial.C).comp b = bR → ((residue R).comp bR).EssFiniteType ∧ ∀ a t : ℕ, ringKrullDim W = a → (letI := ((residue W).comp b).toAlgebra; Algebra.trdeg F (ResidueField W) = t) → ∃ a' t' : ℕ, ringKrullDim R = a' ∧ (letI := ((residue R).comp bR).toAlgebra; Algebra.trdeg F (ResidueField R) = t') ∧ a' + t' = a + t + Fintype.card I := by
  first | exact @GlobalTheory.CDimAlg.ringKrullDim_add_trdeg_of_isComplAt | exact GlobalTheory.CDimAlg.ringKrullDim_add_trdeg_of_isComplAt | (intros; apply GlobalTheory.CDimAlg.ringKrullDim_add_trdeg_of_isComplAt <;> assumption)
