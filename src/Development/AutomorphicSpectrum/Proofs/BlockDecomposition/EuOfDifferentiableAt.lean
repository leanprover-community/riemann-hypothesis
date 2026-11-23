module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Basify
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyLineUnit

@[expose] public section

noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.RmHol
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.RmHol.GelCoef

variable {n : ℕ}

theorem Eu_of_differentiableAt {f : Mat n → ℂ} {z : Mat n} (hf : DifferentiableAt ℂ f z) (a b : Fin n) :
    Eu true a b f z = fderiv ℂ f z (z * Matrix.single a b 1) ∧ Eu false a b f z = 0 := by
  have hR : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ :=
    (hf.hasFDerivAt.restrictScalars ℝ).fderiv
  have hI : z * Matrix.single a b Complex.I = Complex.I • (z * Matrix.single a b (1 : ℂ)) := by
    rw [← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  constructor
  · simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, if_true, hR,
      ContinuousLinearMap.coe_restrictScalars', hI, map_smul, smul_eq_mul]
    linear_combination (-(1 / 2 : ℂ) * fderiv ℂ f z (z * Matrix.single a b (1 : ℂ))) * hII
  · simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, hR, Bool.false_eq_true, if_false,
      ContinuousLinearMap.coe_restrictScalars', hI, map_smul, smul_eq_mul]
    linear_combination ((1 / 2 : ℂ) * fderiv ℂ f z (z * Matrix.single a b (1 : ℂ))) * hII

theorem Eu_congr_germ {f h : Mat n → ℂ} {g : Mat n} (e : f =ᶠ[𝓝 g] h) (s : Bool) (a b : Fin n) :
    Eu s a b f g = Eu s a b h g := by
  simp only [Eu, Rd, Pi.smul_apply, Pi.add_apply, e.fderiv_eq]

end GlobalTheory.CompanionTheory.RmHol.GelCoef
