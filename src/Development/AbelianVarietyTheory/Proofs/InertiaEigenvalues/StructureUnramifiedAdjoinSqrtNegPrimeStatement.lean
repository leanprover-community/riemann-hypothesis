module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StructureUnramifiedAdjoinSqrtNegPrime
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.structure_unramified_adjoin_sqrt_neg_prime : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : FinExt l) (M : IntermediateField ℚ_[l] (Om l)) (y : Om l), M ≤ MaximalUnramifiedExtension l → y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} → K.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} → K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} ∧ K.1 ≤ Ks K 1 ∧ Module.finrank ↥(K0 K) ↥K.1 = 2 ∧ Module.finrank ℚ_[l] ↥(Ks K 1) = (l - 1) / 2 * Module.finrank ℚ_[l] ↥K.1 := by
  first | exact @GlobalTheory.SqrtNegL.structure_sqrt_neg | exact GlobalTheory.SqrtNegL.structure_sqrt_neg | (intros; apply GlobalTheory.SqrtNegL.structure_sqrt_neg <;> assumption)
