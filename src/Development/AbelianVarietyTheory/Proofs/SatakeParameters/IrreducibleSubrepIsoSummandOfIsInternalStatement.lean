module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubrepIsoSummandOfIsInternal
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan

@[expose] public section

open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField

theorem _root_.GlobalTheory.T.irreducible_subrep_iso_summand_of_isInternal : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ : Γ →* GL (Fin a) L) (Us : Fin n → Submodule L (Fin a → L)), DirectSum.IsInternal Us → (∀ m, IsIrrSub τ (Us m)) → ∀ W, IsIrrSub τ W → ∃ m, IsoSub τ W (Us m) := by
  first | exact @GlobalTheory.SplitField.isoSub_summand_of_isInternal | exact GlobalTheory.SplitField.isoSub_summand_of_isInternal | (intros; apply GlobalTheory.SplitField.isoSub_summand_of_isInternal <;> assumption)
