module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeLocalization
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

@[expose] public section

open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

theorem _root_.GlobalTheory.T.glued_lattice_localization : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (T : FinitePlace L → Matrix (Fin n) (Fin n) L), (∀ v, (T v).det ≠ 0) → {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite → ∀ v, locAt v (glued T) = locAt v (frame (T v)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.locAt_glued <;> assumption)
