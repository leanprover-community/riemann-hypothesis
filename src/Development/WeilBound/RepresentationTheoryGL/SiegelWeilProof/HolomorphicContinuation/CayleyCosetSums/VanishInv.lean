module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTauAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Imports
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InnerGen
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SecondCoordMulInner
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

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

theorem vanish_inv (hmn : m < n) (e : ℤ) (y b : M2 n) (hy : InG y) (hb : InG b) (hc : IsUnit y.toBlocks₂₁.det)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, fz m e 0 (y * nU (herm s) * b) * ψ s = 0 := by
  obtain ⟨R, H0, κ, hR, hH0, hκ, hf⟩ := factor y b hy hb hc
  have key : ∀ s, fz m e 0 (y * nU (herm s) * b) * ψ s =
      ((y.det * b.det) ^ e * κ ^ (-(m : ℤ))) *
        (ψ s * (R * Rᴴ - Complex.I • (H0 + herm s)).det⁻¹ ^ m) := by
    intro s
    rw [fz_zero, hf, Matrix.det_mul, Matrix.det_mul, det_nU, mul_one]
    simp only [mul_zpow, _root_.zpow_neg, zpow_natCast, inv_pow]
    ring
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul, core2 hmn R hR H0 hH0 ψ hψ, mul_zero]

end PositivityTheory.Rg.Sw.HSt.L3
