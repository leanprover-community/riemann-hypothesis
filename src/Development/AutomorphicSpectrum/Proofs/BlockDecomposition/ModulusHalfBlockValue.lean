module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctional
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

theorem ordL_pow_div_pow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x y : L}
    (hx : x ≠ 0) (hy : y ≠ 0) (a b : ℕ) :
    ordL (x ^ b / y ^ a) = (b : ℤ) * ordL x - (a : ℤ) * ordL y := by
  have h : x ^ b / y ^ a =
      (((Units.mk0 x hx) ^ (b : ℤ) * (Units.mk0 y hy) ^ (-(a : ℤ)) : Lˣ) : L) := by
    simp [div_eq_mul_inv]
  rw [h, Units.val_mul, GlobalTheory.CompanionTheory.SwapInt.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _),
    GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow]
  simp only [Units.val_mk0]
  ring

theorem absHalf_blockDet_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (qV E w : ℂ) ^ (-((i : ℂ) * b - (j : ℂ) * a) / 2) := by
  intro E _ _ _ a b w i j m hi hj
  have h1 : m.1.val.det ≠ 0 := by
    have := m.1.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have h2 : m.2.val.det ≠ 0 := by
    have := m.2.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hq : 0 < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have ho := ordL_pow_div_pow h1 h2 a b
  rw [hi, hj] at ho
  unfold absHalf
  rw [ho]
  have hs : Real.sqrt ((qV E w : ℝ) ^ (-((b : ℤ) * (i : ℤ) - (a : ℤ) * (j : ℤ)))) =
      (qV E w : ℝ) ^ (-((i : ℝ) * b - (j : ℝ) * a) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le]
    congr 1
    push_cast
    ring
  rw [hs, Complex.ofReal_cpow hq.le, Complex.ofReal_natCast]
  congr 1
  push_cast
  ring

end GlobalTheory.CompanionTheory.CtS
