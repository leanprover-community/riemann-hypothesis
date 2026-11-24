module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexLinearExtensionOfTraceIsometry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_complexLinear_extension_of_traceIsometry' : ∀ (K E : Type) [Field K] [Field E] [Algebra K E] (cj : E → E) (ι : Type) [Fintype ι] (φ : E →+* ℂ) (emb : ι → E →+* ℂ), (∀ y, φ (cj y) = starRingEnd ℂ (φ y)) → (∀ τ y, emb τ (cj y) = starRingEnd ℂ (emb τ y)) → (∀ τ (x : K), emb τ (algebraMap K E x) = φ (algebraMap K E x)) → (∀ y, ∑ τ, emb τ y = φ (algebraMap K E (Algebra.trace K E y))) → ∀ γ : IsoKG K E cj ι, ∃ gC : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ), ∀ x : Fin 4 → E, gC (fun w => emb w.2 (x w.1)) = fun w => φ (algebraMap K E (γ.g x w)) := by
  first | exact @GlobalTheory.exists_complexLinear_extension_of_traceIsometry | exact GlobalTheory.exists_complexLinear_extension_of_traceIsometry | (intros; apply GlobalTheory.exists_complexLinear_extension_of_traceIsometry <;> assumption)
