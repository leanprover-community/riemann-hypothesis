module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorAdelicLatticeCompact
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

theorem _root_.GlobalTheory.T.annihilator_adelic_lattice_compact : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {ψ : AddChar (Ad E) ℂ}, StdPsi ψ → ∀ (S : Finset (Pl E)), (∀ w, w ∉ S → Cond ψ w) → ∀ (L : Set (Af E)), (∀ w, w ∉ S → ∀ t ∈ Formalism.UG.Ov E w, sLoc E w t ∈ L) → (∀ w ∈ S, ∃ N ∈ 𝓝 (0 : w.adicCompletion E), ∀ t ∈ N, sLoc E w t ∈ L) → ∃ C : Set (Af E), IsCompact C ∧ ∀ z : Af E, (∀ a ∈ L, ψ (sFin E (a * z)) = 1) → z ∈ C := by
  first | exact @GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator | exact GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator | (intros; apply GlobalTheory.CompanionTheory.AnnLattice.exists_isCompact_annihilator <;> assumption)
