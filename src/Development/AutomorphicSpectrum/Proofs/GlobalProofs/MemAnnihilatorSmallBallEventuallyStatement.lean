module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemAnnihilatorSmallBallEventually
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
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.adelic_annihilator_box_product : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v))) → ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, (0 : Fv F v) ∈ U v) → annF ψ (Coef.boxA S U) = Coef.boxA S (fun v => annV ψ v (U v)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA <;> assumption)
