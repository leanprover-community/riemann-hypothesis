module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lattice_congruence_iff_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (M : ℕ) (β : GL (Fin n) E), 1 ≤ M → (∀ v, fv F v ∈ hat F (Λ : Set (Fin n → E)) ↔ v ∈ Λ) → (((∀ x, x ∈ Λ ↔ (β : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ Λ) ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ↔ ((∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)), ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ∧ ∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)), ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ y = x)) := by
  first | exact @GlobalTheory.LocGlob.stab_cong_iff_hat | exact GlobalTheory.LocGlob.stab_cong_iff_hat | (intros; apply GlobalTheory.LocGlob.stab_cong_iff_hat <;> assumption)
