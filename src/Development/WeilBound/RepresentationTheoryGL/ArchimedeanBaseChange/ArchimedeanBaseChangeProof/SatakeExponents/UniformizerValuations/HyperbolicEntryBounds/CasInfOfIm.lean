module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramified
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.RingTheory.PiTensorProduct
public import Development.DiscreteGroups.PiInvariants.CasimirInfinity.CasInfOfIm

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchBump, Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchCas, Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchPhi, Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.CasInfOfIm

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchBump =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchBump", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension\npublic import Mathlib.Analysis.Calculus.BumpFunction.Normed\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves\npublic import Mathlib.Analysis.Calculus.BumpFunction.Basic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA

theorem cosh_im_zero (c : ℂ) (hc : c.im = 0) (t : ℝ) : (Complex.cosh (t * c ^ (1 / 2 : ℂ))).im = 0 := by
  set s := c ^ (1 / 2 : ℂ) with hs
  have hsq : s ^ 2 = c := by
    have := Complex.cpow_nat_inv_pow c (n := 2) (by norm_num)
    simpa [hs, one_div] using this
  have him : s.re * s.im = 0 := by
    have h := congrArg Complex.im hsq
    rw [hc, pow_two, Complex.mul_im] at h
    linarith
  rcases mul_eq_zero.1 him with h | h
  · have e : (t : ℂ) * s = ((t * s.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [h]
    rw [e, Complex.cosh_mul_I, ← Complex.ofReal_cos, Complex.ofReal_im]
  · have e : (t : ℂ) * s = ((t * s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [h]
    rw [e, ← Complex.ofReal_cosh, Complex.ofReal_im]

end PositivityTheory.Rg.BcB.F.F0

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchBump =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchCas =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchCas", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA

theorem im_pow_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, (A i j).im = 0) (k : ℕ) (i j : Fin n) :
    ((A ^ k) i j).im = 0 := by
  have hAe : A = (A.map Complex.re).map (Complex.ofRealHom : ℝ →+* ℂ) := by
    ext i j
    apply Complex.ext <;> simp [hA i j]
  rw [hAe, ← RingHom.mapMatrix_apply, ← map_pow, RingHom.mapMatrix_apply]
  simp

end PositivityTheory.Rg.BcB.F.F0

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchCas =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchPhi =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchPhi", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA

theorem entry_le_of_lg {n : ℕ} {y : Mat n} {R : ℝ} (h : lg y ≤ R) (a b : Fin n) :
    ‖y a b‖ ≤ Real.exp R ∧ ‖y⁻¹ a b‖ ≤ Real.exp R := by
  have hterm : ‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2 ≤ ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2) := by
    have h1 : ‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2 ≤ ∑ b', (‖y a b'‖ ^ 2 + ‖y⁻¹ a b'‖ ^ 2) :=
      Finset.single_le_sum (f := fun b' => ‖y a b'‖ ^ 2 + ‖y⁻¹ a b'‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ b)
    exact h1.trans (Finset.single_le_sum (f := fun a' => ∑ b', (‖y a' b'‖ ^ 2 + ‖y⁻¹ a' b'‖ ^ 2))
      (fun _ _ => by positivity) (Finset.mem_univ a))
  have hS0 : 0 ≤ ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2) := by positivity
  have hE : 1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2) ≤ Real.exp R := by
    have hl : Real.log (1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2)) ≤ R := h
    calc 1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2)
        = Real.exp (Real.log (1 + ∑ a, ∑ b, (‖y a b‖ ^ 2 + ‖y⁻¹ a b‖ ^ 2))) :=
          (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp R := Real.exp_le_exp.2 hl
  have k1 : ∀ x : ℝ, x ≤ 1 + x ^ 2 := fun x => by nlinarith [sq_nonneg (x - 1 / 2)]
  constructor
  · nlinarith [k1 ‖y a b‖, sq_nonneg ‖y⁻¹ a b‖]
  · nlinarith [k1 ‖y⁻¹ a b‖, sq_nonneg ‖y a b‖]

theorem isCompact_entries {n : ℕ} (r : ℝ) :
    IsCompact {y : G n | (∀ a b, ‖(y : Mat n) a b‖ ≤ r) ∧ ∀ a b, ‖((y⁻¹ : G n) : Mat n) a b‖ ≤ r} := by
  let B : Set (Mat n) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) r
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hC : IsCompact (B ×ˢ (MulOpposite.op '' B)) := hB.prod (hB.image MulOpposite.continuous_op)
  have h := (Units.isClosedEmbedding_embedProduct (α := Mat n)).isCompact_preimage hC
  convert h using 1
  ext y
  change _ ↔ ((y : Mat n) ∈ B ∧ MulOpposite.op ((y⁻¹ : G n) : Mat n) ∈ MulOpposite.op '' B)
  rw [MulOpposite.op_injective.mem_set_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a _ b _ => mem_closedBall_zero_iff.2 (h1 a b), fun a _ b _ => mem_closedBall_zero_iff.2 (h2 a b)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun a b => mem_closedBall_zero_iff.1 (h1 a trivial b trivial),
      fun a b => mem_closedBall_zero_iff.1 (h2 a trivial b trivial)⟩

end PositivityTheory.Rg.BcB.F.F0

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchPhi =====

-- ===== clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.CasInfOfIm =====
-- clump-header: {"m": "Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.CasInfOfIm", "h": "module\n\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableOf\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramified\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFd\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchBump\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchCas\npublic import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchPhi\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.F0

open PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelA

theorem archEx_of (hG : PositivityTheory.Rg.BcB.E1.GrowthJ) (hC : CompatEx) (hL : Lef) (hV : VCBridge) (hP : LefPair)
    (hK : KerEx) : ArchEx := by
  intro E _ _ _ hE a b l₁ l₂ μ₁ μ₂ μa μb h₁ h₂ ha hb
  haveI : Nontrivial (InfinitePlace E) := _root_.GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace E hE
  haveI : BorelSpace (GA E a) := ⟨rfl⟩
  haveI : BorelSpace (GA E b) := ⟨rfl⟩
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E a b) := ⟨rfl⟩
  have := h₁
  have := h₂
  have := ha
  have := hb
  obtain ⟨D, hD⟩ := hG E a b μ₁ μ₂
  obtain ⟨ν, hν, hν', hcomp⟩ := hC E a b D μa μb
  obtain ⟨-, -, ca, hca0, hca⟩ := GlobalTheory.CompanionTheory.Growth.size_facts E a
  obtain ⟨-, -, cb, hcb0, hcb⟩ := GlobalTheory.CompanionTheory.Growth.size_facts E b
  have LA := fun v : InfinitePlace E => hL a (l₁ v).w (l₁ v).anti
  have LB := fun v : InfinitePlace E => hL b (l₂ v).w (l₂ v).anti
  obtain ⟨bump, T, hT, hbump, hone⟩ := bump_one (InfinitePlace E ⊕ InfinitePlace E)
    (Sum.elim (fun v => cas (infOf (l₁ v).w)) fun v => cas (infOf (l₂ v).w))
    (fun i => by cases i <;> exact cas_infOf_im _)
  obtain ⟨_, hKa⟩ := hK a
  obtain ⟨_, hKb⟩ := hK b
  let Ma : Mods E a := fun v => (LA v).choose
  let Mb : Mods E b := fun v => (LB v).choose
  let Ta : Ops Ma := fun v => (LA v).choose_spec.choose
  let Tb : Ops Mb := fun v => (LB v).choose_spec.choose
  have sa := fun v => (LA v).choose_spec.choose_spec
  have sb := fun v => (LB v).choose_spec.choose_spec
  let ka : List (Bool × ℕ) → Kers Ma := fun w v => ((hKa μa (Ma v)).1 w bump T hbump).choose
  let kb : List (Bool × ℕ) → Kers Mb := fun w v => ((hKb μb (Mb v)).1 w bump T hbump).choose
  exact ⟨{
    D := D
    Ma := Ma
    Mb := Mb
    ν := ν
    ha := ha
    hb := hb
    hν := hν
    hν' := hν'
    compat := hcomp
    c := max ca cb
    c_nonneg := le_max_of_le_left hca0
    ca := fun g h => (hca g h).trans (by gcongr; exact le_max_left _ _)
    cb := fun g h => (hcb g h).trans (by gcongr; exact le_max_right _ _)
    growth := fun κ _ => hD (Io Ma Mb κ)
    Ta := Ta
    Tb := Tb
    vca := fun v k val T' hm => hV a μa (Ma v) (Ta v) k val T' (sa v).1 hm ((sa v).2.2.2 μa k val T' hm).1
    vcb := fun v k val T' hm => hV b μb (Mb v) (Tb v) k val T' (sb v).1 hm ((sb v).2.2.2 μb k val T' hm).1
    lef := fun v k k' val val' T' hm hm' => hP a b μa μb (l₁ v) (l₂ v) _ _ _ _
      ⟨(phiOf_cs μa (Ma v) (Ta v) k val T' hm).1, (phiOf_cs μa (Ma v) (Ta v) k val T' hm).2,
        fun d z hd hz hi => ((sa v).2.2.2 μa k val T' hm).2 d z hd hz hi |>.2⟩
      ⟨(phiOf_cs μb (Mb v) (Tb v) k' val' T' hm').1, (phiOf_cs μb (Mb v) (Tb v) k' val' T' hm').2,
        fun d z hd hz hi => ((sb v).2.2.2 μb k' val' T' hm').2 d z hd hz hi |>.2⟩
    bump := bump
    T := T
    T_nonneg := hT
    isBump := hbump
    ka := ka
    kb := kb
    kera := fun w v => ((hKa μa (Ma v)).1 w bump T hbump).choose_spec
    kerb := fun w v => ((hKb μb (Mb v)).1 w bump T hbump).choose_spec
    one := by simpa [Fintype.prod_sum_type] using hone }⟩

end PositivityTheory.Rg.BcB.F.F0

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.CasInfOfIm =====
