module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteCenterMonicAnnihilator
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

theorem _root_.GlobalTheory.T.cofinite_center_monic_annihilator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (J : Set (Module.End ℂ (Sm E n))), Cofin J → ∀ z ∈ Zalg E n, ∃ p : Polynomial ℂ, p.Monic ∧ ∀ φ : Sm E n, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed | exact GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed | (intros; apply GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed <;> assumption)
