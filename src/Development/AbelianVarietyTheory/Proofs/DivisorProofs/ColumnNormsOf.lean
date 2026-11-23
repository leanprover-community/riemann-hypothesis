module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ColNorms

theorem errUnit_nonneg (N : NumDatum) {T : ℕ} (hT : 1 ≤ T) : 0 ≤ errUnit N T := by
  have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
  have h1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
  have h2 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h3 : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1) h2)
  unfold errUnit
  positivity

theorem kernelBound_ge (N : NumDatum) (δ : Code N) (T : ℕ) (C₁ C₂ : ℝ) (j : ℕ) (lo : RPl N.R → ℝ) (lt : ℝ) (h h' n n' : ℕ) :
    kernelBound_sq N δ T C₁ j lo lt 1 1 1 1 + 2 * (C₂ * errUnit N T) ≤ kernelBound_sq N δ T (C₁ + C₂) j lo lt h h' n n' := by
  have a1 : 0 ≤ Real.log ((h : ℝ) * h') := by exact_mod_cast Real.log_natCast_nonneg (h * h')
  have a2 : 0 ≤ Real.log ((n : ℝ) * n') := by exact_mod_cast Real.log_natCast_nonneg (n * n')
  unfold kernelBound_sq errUnit
  simp only [Nat.cast_one, mul_one, Real.log_one]
  nlinarith

theorem SmallDatum.mono {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    {S : Finset (HeightOneSpectrum (𝓞 E))} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {c : ℕ}
    {Ξ : HomE E a b → K} {β β' : ℝ} (h : SmallDatum S N N' c Ξ β) (hβ : β ≤ β') : SmallDatum S N N' c Ξ β' :=
  ⟨h.1, h.2.1, fun σ x => (h.2.2 σ x).trans hβ⟩

end GlobalTheory.ColNorms
