module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

theorem _root_.GlobalTheory.T.algebraicNumbers_padicPlaces_facts : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (σ : K →+* ℂ) (ι : K →+* ℂ_[p]), (∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k, σ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (σ k) = ι k) ∧ (∀ w : HeightOneSpectrum (𝓞 K), (∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) → ∀ x : K, w.valuation K x ≤ 1 → ‖ι x‖ ≤ 1) ∧ ∀ (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (r : ℚ), Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)))‖ = 1 := by
  first | exact @GlobalTheory.MomPlace.places | exact GlobalTheory.MomPlace.places | (intros; apply GlobalTheory.MomPlace.places <;> assumption)
