module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueAnnihilatorOfNotStandardColumnFormA
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

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.exists_residue_annihilator_of_not_standard_column_form_alt : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) O, (¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) → ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ u : Fin r ⊕ Fin t → O, (fun i => algebraMap O K (u i)) ∈ Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) → (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0 := by
  first | exact @GlobalTheory.exists_residue_annihilator_of_not_standard_column_form | exact GlobalTheory.exists_residue_annihilator_of_not_standard_column_form | (intros; apply GlobalTheory.exists_residue_annihilator_of_not_standard_column_form <;> assumption)
