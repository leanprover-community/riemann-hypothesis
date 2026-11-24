module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleReflectionRootBorelDecomp
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

theorem _root_.GlobalTheory.T.simple_reflection_root_borel_decomp : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ x : L, x ≠ 0 →
    ∃ b : GU σ n, IsBorelU b ∧
      chiDeltaU q (fun k => (χ k : ℂ)) b = (((χ i : ℂ) / (χ j : ℂ)) / (q : ℂ) ^ 2) ^ (-ordL x) ∧
      sR σ hU.1 a h * uR σ hU.1 a h x = b * (sR σ hU.1 a h * uR σ hU.1 a h x⁻¹ * sR σ hU.1 a h) := by
  first | exact @GlobalTheory.CompanionTheory.SwapFactor.sR_uR_factor | exact GlobalTheory.CompanionTheory.SwapFactor.sR_uR_factor | (intros; apply GlobalTheory.CompanionTheory.SwapFactor.sR_uR_factor <;> assumption)
