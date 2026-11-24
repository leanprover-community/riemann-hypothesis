module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EchEqOneIff
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralEqSumResidueRepresentative
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

open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.schwartzBruhatIntegral_eq_sum_residueRepresentatives : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ : Matrix κ ι ℚ → ℂ), 0 < R → HasLevel R φ → haar φ = ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ * ∑ n : κ → ι → Fin (R * R), φ (rep R n) := by
  first | exact @GlobalTheory.SW.FourierJ.haar_eq_sum_rep | exact GlobalTheory.SW.FourierJ.haar_eq_sum_rep | (intros; apply GlobalTheory.SW.FourierJ.haar_eq_sum_rep <;> assumption)
