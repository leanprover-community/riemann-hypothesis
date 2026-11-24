module

public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveVectorNormNegHyperbolicPair
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions

theorem _root_.GlobalTheory.T.exists_primitive_vector_norm_neg_hyperbolicPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], CMData F E → ∀ (S : HSpace E) (Λ : Submodule (𝓞 E) S.V), Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → (∃ x : 𝓞 E, (x : E) + star (x : E) = 1) → ∀ (e f : S.V) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → S.hT e e = 0 → S.hT f f = 0 → S.hT e f = 1 → (∀ x ∈ c, x • e ∈ Λ) → (∀ y ∈ Λ, S.hT f y ∈ c) → ∀ T : ℕ, T ≠ 0 → ∃ z : S.V, z ∈ Submodule.span E {e, f} ∧ z ∈ Λ ∧ S.hT z z = -((T : ℕ) : E) ∧ ∀ γ : E, γ • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = γ := by
  first | exact @GlobalTheory.HypPrimVec.exists_primitive_norm_neg | exact GlobalTheory.HypPrimVec.exists_primitive_norm_neg | (intros; apply GlobalTheory.HypPrimVec.exists_primitive_norm_neg <;> assumption)
