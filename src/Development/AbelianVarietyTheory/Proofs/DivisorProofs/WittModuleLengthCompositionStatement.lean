module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.WittVector.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittModuleLengthComposition
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
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.RingTheory.Bialgebra.Basic

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.witt_module_length_composition : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B C : Type) [AddCommGroup A] [Module (WittVector p k) A] [AddCommGroup B] [Module (WittVector p k) B] [AddCommGroup C] [Module (WittVector p k) C], (∀ (u : B →ₗ[(WittVector p k)] A) (v : C →ₗ[(WittVector p k)] B), Function.Injective u → Module.length (WittVector p k) (A ⧸ LinearMap.range (u ∘ₗ v)) = Module.length (WittVector p k) (A ⧸ LinearMap.range u) + Module.length (WittVector p k) (B ⧸ LinearMap.range v)) ∧ (Module.Free (WittVector p k) A → Module.Finite (WittVector p k) A → ∀ (n : ℕ) (u : A →ₗ[(WittVector p k)] A), (∀ a, u a = p ^ n • a) → Module.length (WittVector p k) (A ⧸ LinearMap.range u) = (n * Module.finrank (WittVector p k) A : ℕ)) ∧ ∀ L L' : Submodule (WittVector p k) A, L ≤ L' → Module.length (WittVector p k) (A ⧸ L) = Module.length (WittVector p k) (A ⧸ L') → Module.length (WittVector p k) (A ⧸ L) ≠ ⊤ → L = L' := by
  first | exact @GlobalTheory.Dieu.colength_add_and_pow_and_eq | exact GlobalTheory.Dieu.colength_add_and_pow_and_eq | (intros; apply GlobalTheory.Dieu.colength_add_and_pow_and_eq <;> assumption)
