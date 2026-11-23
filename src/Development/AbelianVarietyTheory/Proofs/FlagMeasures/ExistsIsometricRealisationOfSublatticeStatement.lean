module

public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricRealisationOfSublattice
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
import Formalism.HermitianLattices.StatementLat

@[expose] public section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

theorem _root_.GlobalTheory.T.exists_isometric_realisation_of_sublattice' : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (R : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → R.FG → ∃ (j : ℕ) (i : Matrix (Fin n) (Fin j) K) (X' : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ) (P : InfinitePlace K → Matrix (Fin n) (Fin j) ℂ) (B : Submodule (𝓞 K) (Fin j → K)), j = rkK R ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, (P w)ᴴ * P w = 1) ∧ (∀ w, (X w)⁻¹ * i.map w.embedding = P w * (X' w)⁻¹) ∧ B.FG ∧ Submodule.span K (B : Set (Fin j → K)) = ⊤ ∧ (∀ y ∈ B, i *ᵥ y ∈ R) ∧ (∀ r ∈ R, ∃ y ∈ B, i *ᵥ y = r) ∧ largestSize (Pi.basisFun K (Fin j)) X' B = largestSize (Pi.basisFun K (Fin n)) X R := by
  first | exact @GlobalTheory.exists_isometric_realisation_of_sublattice | exact GlobalTheory.exists_isometric_realisation_of_sublattice | (intros; apply GlobalTheory.exists_isometric_realisation_of_sublattice <;> assumption)
