module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.LiftSingleAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ShiftPow
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.sub_eq_zero_iff :
    ∀ (ι κ : Type) [Fintype ι] (b : Fam ι κ) (F : KF ι κ), b.sub F = 0 ↔ ∀ Λ h, b.Mem Λ h → evK Λ h F = 0 := by
  intro ι κ _ b F
  have key : ∀ lam : Fin b.r → ℂ, ev lam (b.sub F) =
      evK (fun i => b.Λ i + ∑ j, (b.emb i j : ℂ) * lam j) (fun k => ev lam (b.h k)) F := fun lam => by
    have : (ev lam).comp b.sub = evK (fun i => b.Λ i + ∑ j, (b.emb i j : ℂ) * lam j) (fun k => ev lam (b.h k)) :=
      MvPolynomial.ringHom_ext (fun f => by
        simpa [Fam.sub, evK] using (UpperTheory.ConvolutionTheory.FX.subst ι _ b.Λ b.emb f).1 lam) (fun k => by simp [Fam.sub, evK])
    exact RingHom.congr_fun this F
  refine ⟨fun h0 Λ h ⟨lam, h1, h2⟩ => ?_, fun h => UpperTheory.ConvolutionTheory.FX.ev_inj _ _ fun lam => ?_⟩
  · rw [funext h1, funext h2, ← key, h0, map_zero]
  · rw [key]
    exact h _ _ ⟨lam, fun _ => rfl, fun _ => rfl⟩
