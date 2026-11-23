module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryConjSplitLatticeOfLocal
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.exists_unitary_conj_split_lattice_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → GlobalTheory.UTrans.IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ GlobalTheory.UTrans.hf (c : E →+* E) G z z = 0) → ∀ L L₀ : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (π γ₀ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (b k : ℕ), π * π = π → (∀ v w, GlobalTheory.UTrans.hf (c : E →+* E) G (π.mulVec v) w = GlobalTheory.UTrans.hf (c : E →+* E) G v (π.mulVec w)) → π.mulVec x = x → GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 → (∀ v ∈ L₀, π.mulVec v ∈ L₀) → 0 < b → (∀ v ∈ L, b • v ∈ L₀) → (∀ v ∈ L₀, b • v ∈ L) → GlobalTheory.UTrans.IsU (c : E →+* E) G γ₀ → k.Coprime b → (∀ v ∈ L, k • γ₀.mulVec v ∈ L₀) → (∀ v ∈ L₀, k • γ₀⁻¹.mulVec v ∈ L) → ∃ γ : Matrix (Fin n) (Fin n) E, GlobalTheory.UTrans.IsU (c : E →+* E) G γ ∧ ∀ v ∈ L, (γ⁻¹ * π * γ).mulVec v ∈ L := by
  first | exact @GlobalTheory.UTrans.exists_isU_conj_mem | exact GlobalTheory.UTrans.exists_isU_conj_mem | (intros; apply GlobalTheory.UTrans.exists_isU_conj_mem <;> assumption)
