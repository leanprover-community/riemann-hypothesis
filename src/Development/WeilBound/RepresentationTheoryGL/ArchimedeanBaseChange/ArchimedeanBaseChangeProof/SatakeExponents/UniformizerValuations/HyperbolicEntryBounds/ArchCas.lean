module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves

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

theorem cas_infOf_im' {n : ℕ} (lam : Fin n → ℤ) : (cas (infOf lam)).im = 0 := by
  have hχ : ∀ s a, (infOf lam s a).im = 0 := by
    intro s a
    cases s <;> simp [infOf]
  have hg : ∀ s, (GlobalTheory.Dec.gelfVal (infOf lam s) 2).im = 0 := by
    intro s
    unfold GlobalTheory.Dec.gelfVal
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    apply im_pow_entry
    intro i j
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    split_ifs <;> simp [hχ]
  simp [cas, hg]

end PositivityTheory.Rg.BcB.F.F0

end
