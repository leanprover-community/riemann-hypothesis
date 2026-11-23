module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestTContinuousHasCompactSupport
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
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.continuous_and_hasCompactSupport_testT : ∀ (F : Type) [Field F] [NumberField F] (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)), Continuous ρ → HasCompactSupport ρ → (∀ v, IsCompact (U v) ∧ IsOpen (U v)) → Continuous (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) ∧ HasCompactSupport (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.testT ρ S U) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.TestC.testT_continuous_hasCompactSupport <;> assumption)
