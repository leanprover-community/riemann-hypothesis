module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameValuesGaloisCharFormResidueUnitCharacter
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.tameValues_galoisChar_form_residue_unit_character : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {M : Type} [CommGroup M]
    (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (m : ℕ),
    IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal →
    (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1) →
    (∀ u u' : 𝓞 E, u ∉ P.asIdeal → u' ∉ P.asIdeal → NX.tameVal φ P e (u * u') = NX.tameVal φ P e u * NX.tameVal φ P e u') ∧
    ∀ u u' : 𝓞 E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal → NX.tameVal φ P e u = NX.tameVal φ P e u' := by
  first | exact @GlobalTheory.TameValChar.main | exact GlobalTheory.TameValChar.main | (intros; apply GlobalTheory.TameValChar.main <;> assumption)
