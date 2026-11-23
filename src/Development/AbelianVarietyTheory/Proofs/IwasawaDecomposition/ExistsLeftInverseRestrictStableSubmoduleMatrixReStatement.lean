module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseRestrictStableSubmoduleMatrixRe
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.exists_leftInverse_restrict_stable_submodule_matrixRep : ∀ {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (V : Submodule L (Fin a → L)), IsInv τ V → ∃ (b : ℕ) (E : Matrix (Fin a) (Fin b) L) (D : Matrix (Fin b) (Fin a) L) (σ : Γ →* GL (Fin b) L), D * E = 1 ∧ LinearMap.range E.mulVecLin = V ∧ ∀ g, ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) = D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E ∧ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E = E * ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
  exact @GlobalTheory.StableSubMat.exists_restrict
