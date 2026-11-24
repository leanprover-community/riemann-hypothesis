module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.tameInertia_representative_residue : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime], IsPlaceOver (F := E) A P → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ((g : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (σ : G E Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g), σ ∈ Ine (F := E) A → IsGenSys ζ → TameCoupled A κ σ ζ → (∀ A' : ValuationSubring Ω, IsPlaceOver (F := E) A' P → σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A) → ∀ u : 𝓞 E, NX.TameRep P 1 σ u → ∃ a : ℕ, a.Coprime g ∧ u - (a : 𝓞 E) ∈ P.asIdeal ∧ algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (a : ZMod g) = ζ 1 := by
  first | exact @GlobalTheory.tameRep_residue | exact GlobalTheory.tameRep_residue | (intros; apply GlobalTheory.tameRep_residue <;> assumption)
