module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliAuxiliaryStatement
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

theorem _root_.GlobalTheory.T.capelli_restrict_levi : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (q : Polynomial ℂ) (F : Sm E (r + s)), (∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ m, (Polynomial.aeval (cap (a := r) τ u) q G).1 m = (Polynomial.aeval (capR r s τ u) q F).1 (lev (Ad E) r s (m, 1))) ∧ (∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ m, (Polynomial.aeval (cap (a := s) τ u) q G).1 m = (Polynomial.aeval (capS r s τ u) q F).1 (lev (Ad E) r s (1, m))) := by
  exact @GlobalTheory.CompanionTheory.CTFin.capelli_restrict
