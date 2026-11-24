module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedIntegersStableSubgroupEqDoubleOrthogonal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.boundedIntegersStableSubgroup_eq_doubleOrthogonal : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ₀ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ HeightOneSpectrum.adicCompletionIntegers F v, ψ₀ (x * y) = 1) ↔ x ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ A : AddSubgroup (κ → Fv F v), (∀ c ∈ HeightOneSpectrum.adicCompletionIntegers F v, ∀ t ∈ A, c • t ∈ A) →
    (∃ c : Fv F v, c ≠ 0 ∧ ∀ t ∈ A, ∀ k, c * t k ∈ HeightOneSpectrum.adicCompletionIntegers F v) →
    ∀ t : κ → Fv F v, (∀ y : κ → Fv F v, (∀ s ∈ A, ψ₀ (s ⬝ᵥ y) = 1) → ψ₀ (t ⬝ᵥ y) = 1) → t ∈ A := by
  first | exact @GlobalTheory.LatticeDual.mem_of_mem_doubleOrth | exact GlobalTheory.LatticeDual.mem_of_mem_doubleOrth | (intros; apply GlobalTheory.LatticeDual.mem_of_mem_doubleOrth <;> assumption)
