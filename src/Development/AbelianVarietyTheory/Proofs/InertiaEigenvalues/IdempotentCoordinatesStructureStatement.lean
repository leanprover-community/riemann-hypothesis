module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentCoordinatesStructure
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

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.idempotentCoordinates_structure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), e * e = e → star e = 1 - e → (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) ∧ (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) ∧ (∀ p, A.NL (Hyp.cc A e p) = p.1 * p.2) ∧ (∀ (ψ : AddChar F ℂ) (x : A.K) (p q : A.K × A.K), A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) ∧ (∀ (s : A.K) p, s • Hyp.cc A e p = Hyp.cc A e (s * p.1, s * p.2)) ∧ ∀ s : A.Kˣ, IsUnit (Hyp.cc A e ((s : A.K), 1)) := by
  first | exact @GlobalTheory.JR.Hyp.coord_structure | exact GlobalTheory.JR.Hyp.coord_structure | (intros; apply GlobalTheory.JR.Hyp.coord_structure <;> assumption)
