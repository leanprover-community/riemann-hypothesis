module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeGaussianSumOfLengthEqTsumStabilizerCosets
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.latticeGaussianSumOfLength_eq_tsum_stabilizer_cosets : ∀ (I : AutInst) (s : Bool) (x : Fin I.n → I.E), star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s → ∃ (ι : Type) (_ : Countable ι) (r : ι → I.GA), (∀ i, r i ∈ I.GFset) ∧ (∀ γ ∈ I.GFset, ∃! i, γ * (r i)⁻¹ ∈ stabF I x) ∧ ∀ g, gaussSum I (sgn I.E s) g = ∑' i, gaussAt I x (r i * g) := by
  first | exact @GlobalTheory.StabCosets.gaussSum_cosets | exact GlobalTheory.StabCosets.gaussSum_cosets | (intros; apply GlobalTheory.StabCosets.gaussSum_cosets <;> assumption)
