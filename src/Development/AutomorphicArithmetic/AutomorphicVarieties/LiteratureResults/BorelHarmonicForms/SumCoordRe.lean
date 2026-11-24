module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem sum_coord_re {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (z : Cinf E) :
    ∑ τ : E →+* ℂ, coord τ z = ((2 * ∑ w : InfinitePlace E, (z w).re : ℝ) : ℂ) := by
  have h := congrArg Multiplicative.toAdd
    (GlobalTheory.GKCoh.Tests.prod_coord (M := Multiplicative ℂ) Multiplicative.ofAdd z)
  simp only [toAdd_prod, toAdd_mul, toAdd_ofAdd, Complex.add_conj] at h
  rw [h, Finset.mul_sum, Complex.ofReal_sum]

theorem UpperTheory.V.Lit.Bor.twEx :
    UpperTheory.V.Lit.Bor.TwEx := by
  intro E _ _ _ a _ r
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (r / (2 * ((a : ℝ) * Fintype.card (InfinitePlace E))))
  refine ⟨_, ⟨_, hν⟩, fun X φ => ?_⟩
  rw [lie_mulChi, GlobalTheory.CuspRep.AlgExpo.dchi_eq_sum]
  simp only [(GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 _ hν, ← Finset.mul_sum]
  rw [sum_coord_re, ← Complex.ofReal_mul]
  have e : ell E a X = (∑ w : InfinitePlace E, ((Matrix.of X).trace w).re) /
      ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
    simp [ell, Matrix.trace]
  rw [e]
  congr 4
  ring
