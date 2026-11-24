module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCosetTranslateMemOfCover
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

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.lattice_coset_translate_mem_of_cover : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K) (z₀ : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z₀).map (algebraMap O K) → (∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ (g' : GL (Fin r) K) (z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), (x + (ϖ ^ N • z).map (algebraMap O K)) * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K)) → ∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O, (x + (ϖ ^ N • z).map (algebraMap O K)) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) := by
  first | exact @GlobalTheory.coset_translate_mem_of_cover | exact GlobalTheory.coset_translate_mem_of_cover | (intros; apply GlobalTheory.coset_translate_mem_of_cover <;> assumption)
