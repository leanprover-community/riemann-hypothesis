module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubfieldAdjoinRootsOfUnityEmbeddingComplex
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

@[expose] public section


theorem _root_.GlobalTheory.T.exists_subfield_adjoin_rootsOfUnity_embedding_complex : ∀ {L0 K : Type} [Field L0] [Field K] (s : L0 →+* K) (t : L0 →+* ℂ) (Z : Set K), (∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1) → ∃ (E : Subfield K) (j : E →+* ℂ), (∀ x, s x ∈ E) ∧ Z ⊆ E ∧ ∀ x (hx : s x ∈ E), j ⟨s x, hx⟩ = t x := by
  first | exact @GlobalTheory.adjoin_roots_of_unity_embeds_complex | exact GlobalTheory.adjoin_roots_of_unity_embeds_complex | (intros; apply GlobalTheory.adjoin_roots_of_unity_embeds_complex <;> assumption)
