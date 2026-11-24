module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix SchwartzMap ComplexConjugate

namespace GlobalTheory.CompanionTheory.QuadChirp

theorem ofReal_re_trace {m n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    (((Matrix.trace (b * (Aᴴ * A))).re : ℝ) : ℂ) = Matrix.trace (b * (Aᴴ * A)) := by
  have h : (starRingEnd ℂ) (Matrix.trace (b * (Aᴴ * A))) = Matrix.trace (b * (Aᴴ * A)) := by
    rw [show (starRingEnd ℂ) (Matrix.trace (b * (Aᴴ * A))) = star (Matrix.trace (b * (Aᴴ * A))) from rfl,
      ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hb, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.1 h

theorem coord_hasTemperateGrowth {m n : ℕ} (l : Fin m) (i : Fin n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => u l i) :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) l)).hasTemperateGrowth

theorem conj_coord_hasTemperateGrowth {m n : ℕ} (l : Fin m) (i : Fin n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => star (u l i)) :=
  ((Complex.conjCLE.toContinuousLinearMap.comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i)).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) l)).hasTemperateGrowth

theorem trace_hasTemperateGrowth {m n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) :
    Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) := by
  have heq : (fun u : Fin m → Fin n → ℂ => Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) =
      fun u => ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m, b i j * (star (u l j) * u l i) := by
    funext u
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Finset.mul_sum]
  rw [heq]
  refine Function.HasTemperateGrowth.sum fun i _ => Function.HasTemperateGrowth.sum fun j _ =>
    Function.HasTemperateGrowth.sum fun l _ => ?_
  exact (Function.HasTemperateGrowth.const (b i j)).mul
    ((GlobalTheory.CompanionTheory.QuadChirp.conj_coord_hasTemperateGrowth l j).mul (GlobalTheory.CompanionTheory.QuadChirp.coord_hasTemperateGrowth l i))

theorem chirp_hasTemperateGrowth {m n : ℕ} (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ =>
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
        Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u)))) := by
  have hre : Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ =>
      k * (Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))).re) :=
    (Function.HasTemperateGrowth.const k).mul
      (Complex.reCLM.hasTemperateGrowth.comp (GlobalTheory.CompanionTheory.QuadChirp.trace_hasTemperateGrowth b))
  have hcomp := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp hre
  convert hcomp using 1
  funext u
  rw [Function.comp_apply, GlobalTheory.Published.Metaplectic.eChar_apply]
  congr 1
  have hT := GlobalTheory.CompanionTheory.QuadChirp.ofReal_re_trace b hb (Matrix.of u)
  rw [Complex.ofReal_mul]
  conv_lhs => rw [← hT]
  ring

theorem exists_schwartz_chirp_mul :
    ∀ (m n : ℕ) (k : ℝ) (b : Matrix (Fin n) (Fin n) ℂ), bᴴ = b →
      ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
        ⇑ψ = fun u => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) *
          Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * φ u := by
  intro m n k b hb φ
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u : Fin m → Fin n → ℂ => Complex.exp (2 * Real.pi *
    Complex.I * (k : ℂ) * Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u)))) φ, ?_⟩
  funext u
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.CompanionTheory.QuadChirp.chirp_hasTemperateGrowth k b hb), smul_eq_mul]

end GlobalTheory.CompanionTheory.QuadChirp
