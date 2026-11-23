module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperModelGenericFibreCompare
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

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.proper_model_generic_fibre_compare : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [IsProper s] (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (C : Type) [Field C] [Algebra O C] [Algebra C Ω'] (s' : X' ⟶ Spec (CommRingCat.of C)), ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → Function.Injective (algebraMap O C) → IsPullback f s' s (Spec.map (CommRingCat.ofHom (algebraMap O C))) → ξ' ≫ s' = Spec.map (CommRingCat.ofHom (algebraMap C Ω')) → Dominates ξ' ξ f i → IsCptGen ξ → IsCptGen ξ' → ConstClosed O Ω → ∀ (L : Lat ξ Ω) (t' : Ω'), L.IsVBOn (genFibre O ξ) 1 ⊤ → (∀ p' : Cpt ξ', (L.pull ξ' f i.toAddMonoidHom).IsGenAt p' t') → ∃ (t : Ω) (c : C), (∀ p ∈ genFibre O ξ, L.IsGenAt p t) ∧ t' = algebraMap C Ω' c * i t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_extension | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_extension | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_gen_of_extension <;> assumption)
