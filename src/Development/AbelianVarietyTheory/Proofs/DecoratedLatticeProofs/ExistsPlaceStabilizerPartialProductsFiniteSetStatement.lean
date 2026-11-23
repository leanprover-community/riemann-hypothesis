module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPlaceStabilizerPartialProductsFiniteSet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open Filter Topology

theorem _root_.GlobalTheory.T.exists_placeStabilizer_partialProducts_finiteSet : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (κ : GA D S), IsSelfDualC S L → InK S L P κ → ∀ Fs : Finset (Pl D), ∃ l : List (GA D S), (∀ y ∈ l, ∃ v, P v ∧ InK S L (· = v) y) ∧ (∀ i j, infPart D (Formalism.L2.Theta.mt S l.prod i j) = infPart D (Formalism.L2.Theta.mt S κ i j)) ∧ (∀ w ∈ Fs, ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S l.prod i j) = GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S κ i j)) ∧ ∀ w, w ∉ Fs → ∀ i j, GlobalTheory.FinPl.compAt D w (Formalism.L2.Theta.mt S l.prod i j) = GlobalTheory.FinPl.compAt D w ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) := by
  first | exact @GlobalTheory.PlaceProducts.finite_place_products | exact GlobalTheory.PlaceProducts.finite_place_products | (intros; apply GlobalTheory.PlaceProducts.finite_place_products <;> assumption)
