module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocSec
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTauAlt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

open scoped Matrix.Norms.Elementwise

def holomorphicScalarSection (m : ℕ) (e : ℤ) (x : M2 n) : ℂ := x.det ^ e * (u1 x).det ^ (-(m : ℤ))

def WM (x : M2 n) : Matrix (Fin n) (Fin n) ℂ :=
  (-(Complex.I • x.toBlocks₁₁) + x.toBlocks₁₂) - zOfE x * u2 x

def CauchyRiemannFacts : Prop :=
  (∀ (n m : ℕ) (e : ℤ) (y : GR n), F0 m 0 e y = holomorphicScalarSection m e (mR y)) ∧
  ∀ (n : ℕ) (x : M2 n), x.det ≠ 0 → (u1 x).det ≠ 0 →
    DifferentiableAt ℂ zOfE x ∧ (∀ (m : ℕ) (e : ℤ), DifferentiableAt ℂ (holomorphicScalarSection m e) x) ∧
    (∀ Q, fderiv ℂ zOfE x (x * lowQ Q) = 0 ∧ ∀ (m : ℕ) (e : ℤ), fderiv ℂ (holomorphicScalarSection m e) x (x * lowQ Q) = 0) ∧
    (∀ R, fderiv ℂ zOfE x (x * sig (lowQ R)) = WM x * Rᴴ * (u1 x)⁻¹) ∧
    (InG x → (WM x).det ≠ 0)

end PositivityTheory.Rg.Sw.HSt.CR
