module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.DFinsupp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChange
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem _root_.GlobalTheory.T.block_mulVec_decomposition_map_of_decomposition : ∀ {K L : Type} [Field K] [Field L] (φ : K →+* L) {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))), ∃ e' : (Fin n → L) ≃ₗ[L] ((Fin r → L) × (Fin t → L)), ∀ (M : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin r) (Fin r) K) (d : Fin t → K), (∀ u, e (M.mulVec u) = (P.mulVec (e u).1, fun c => d c * (e u).2 c)) → ∀ u, e' ((M.map φ).mulVec u) = ((P.map φ).mulVec (e' u).1, fun c => φ (d c) * (e' u).2 c) := by
  first | exact @GlobalTheory.blockDecomposition_baseChange | exact GlobalTheory.blockDecomposition_baseChange | (intros; apply GlobalTheory.blockDecomposition_baseChange <;> assumption)
