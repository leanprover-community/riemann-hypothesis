module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetInducedTwoCharacters
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

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.jacquet_induced_two_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), JacquetOfInducedFiltration k → IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  first | exact @GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional | exact GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional | (intros; apply GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional <;> assumption)
