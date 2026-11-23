module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantAll
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.BurnsideIff

theorem eq_bot_or_top_of_span_eq_top {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (h : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, ((M g).map (algebraMap k K)).mulVec x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5; revert Γ k K h_3 h_4 h_5 r M h W hW; exact @_root_.GlobalTheory.InvariantBotOrTop.main)
  | exact @_root_.GlobalTheory.InvariantBotOrTop.main
  | exact _root_.GlobalTheory.InvariantBotOrTop.main
  | (apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InvariantBotOrTop.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InvariantBotOrTop.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InvariantBotOrTop.main ..)

end GlobalTheory.BurnsideIff
