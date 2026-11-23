module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomCotangentPullbackInjectiveOfSq
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

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A] [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A), (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) → Function.Injective (GlobalTheory.PDiv.cotMap f) := by
  first | exact @GlobalTheory.PDiv.cotMap_injective_of_sq | exact GlobalTheory.PDiv.cotMap_injective_of_sq | (intros; apply GlobalTheory.PDiv.cotMap_injective_of_sq <;> assumption)
