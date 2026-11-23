module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainShortExactOfInjectiveTerms
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.etaleCochain_shortExact_of_injective_terms : ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, (∀ a : Cochain S.X₁ I n, ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a) ∧ (∀ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = 0 → ∃ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = b) ∧ ∀ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = 0 → c = 0 := by
  first | exact @GlobalTheory.EtC.cochain_shortExact_of_injective | exact GlobalTheory.EtC.cochain_shortExact_of_injective | (intros; apply GlobalTheory.EtC.cochain_shortExact_of_injective <;> assumption)
