module

public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiagonalTorusTransitiveGenericCharacters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.diagonal_torus_transitive_generic_characters : ∀ (k : Type) [Field k] [Finite k] (n t : ℕ) (ψ ψ' : AddChar k ℂ) (χ χ' : ℕ → MulChar k ℂ), ψ ≠ 1 → ψ' ≠ 1 → ∃ d : Fin n → kˣ, ∀ M : Matrix (Fin n) (Fin n) k, (InJ n t n false M ↔ InJ n t n false (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1))) ∧ lamJ ψ' χ' n t 0 n M = (lamJ ψ χ n t 0 n (diagonal (fun i => ((d i)⁻¹ : kˣ).1) * M * diagonal (fun i => (d i).1)))⁻¹ := by
  first | exact @GlobalTheory.St.G.Torus.torus_transitive | exact GlobalTheory.St.G.Torus.torus_transitive | (intros; apply GlobalTheory.St.G.Torus.torus_transitive <;> assumption)
