module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ProdAbsNormPowValuationTwoLe
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.prod_absNorm_pow_valuation_two_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ), (∀ v ∈ S, v.valuation F 2 = WithZero.exp (-(e v : ℤ))) → ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ 2 ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow | exact GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow | (intros; apply GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow <;> assumption)
