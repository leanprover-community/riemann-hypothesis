module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomFactorThroughSplitInjection
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.bialgHom_factor_through_split_injection : ∀ (O : Type) [CommRing O] (A B D : Type) [CommRing A] [CommRing B] [CommRing D] [Bialgebra O A] [Bialgebra O B] [Bialgebra O D] (j : B →ₐc[O] A) (ρ : A →ₗ[O] B) (f : D →ₐc[O] A), (∀ b, ρ (j b) = b) → (∀ d, f d ∈ Set.range j) → ∃ g : D →ₐc[O] B, ∀ d, j (g d) = f d := by
  first | exact @GlobalTheory.bialgHom_factor_through_split | exact GlobalTheory.bialgHom_factor_through_split | (intros; apply GlobalTheory.bialgHom_factor_through_split <;> assumption)
