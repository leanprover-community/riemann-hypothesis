module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseOneAddPreservingAdelicCompletion
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_inverse_one_add_preserving_adelicCompletion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (N : ℕ) (e : FiniteAdeleRing (𝓞 F) F), (∀ v, e v ∈ v.adicCompletionIntegers F) → (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∉ v.asIdeal → e v = 0) → ∀ X : Matrix (Fin n) (Fin n) (RA F E), (∀ z ∈ hat F (L : Set (Fin n → E)), X *ᵥ z ∈ hat F (L : Set (Fin n → E))) → ∃ W : Matrix (Fin n) (Fin n) (RA F E), (1 + (e ⊗ₜ[F] (1 : E) : RA F E) • (N • X)) * W = 1 ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), W *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat | exact GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat | (intros; apply GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat <;> assumption)
