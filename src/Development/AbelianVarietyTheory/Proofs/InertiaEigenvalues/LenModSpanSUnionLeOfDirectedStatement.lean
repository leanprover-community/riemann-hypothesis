module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenModSpanSUnionLeOfDirected
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.SetTheory.ZFC.PSet
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition



theorem _root_.GlobalTheory.T.lenMod_span_sUnion_le_of_directed' : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S : Set (Set M)) (H : Submodule O M) (N : ℕ∞), (∀ A ∈ S, ∀ B ∈ S, ∃ C ∈ S, A ⊆ C ∧ B ⊆ C) → (∀ A ∈ S, BlochKatoDuality.lenMod (Submodule.span O A) H ≤ N) → BlochKatoDuality.lenMod (Submodule.span O (⋃₀ S)) H ≤ N := by
  first | exact @GlobalTheory.Pass.LocDirect.lenMod_span_sUnion_le_of_directed | exact GlobalTheory.Pass.LocDirect.lenMod_span_sUnion_le_of_directed | (intros; apply GlobalTheory.Pass.LocDirect.lenMod_span_sUnion_le_of_directed <;> assumption)
