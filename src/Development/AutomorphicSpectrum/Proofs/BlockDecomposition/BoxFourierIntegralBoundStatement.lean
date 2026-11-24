module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxFourierIntegralBound
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

theorem _root_.GlobalTheory.T.box_fourier_integral_bound : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, (∀ x, ‖ψ x‖ = 1) → Continuous ψ → ∀ (L : AddSubgroup (Af E)), IsCompact (L : Set (Af E)) → IsOpen (L : Set (Af E)) → ∀ (c z : Fin k → Af E), ‖∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k‖ ≤ (nuFin E k).real (boxL (L : Set (Af E)) c) ∧ (∫ f, (((boxL (L : Set (Af E)) c).indicator (fun _ => (1 : ℝ)) f : ℝ) : ℂ) * ψ (sFin E (∑ i, f i * z i)) ∂nuFin E k ≠ 0 → ∀ i, ∀ a ∈ L, ψ (sFin E (a * z i)) = 1) := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main | exact GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main | (intros; apply GlobalTheory.CompanionTheory.CutOff.FinFT.box_fourier_main <;> assumption)
