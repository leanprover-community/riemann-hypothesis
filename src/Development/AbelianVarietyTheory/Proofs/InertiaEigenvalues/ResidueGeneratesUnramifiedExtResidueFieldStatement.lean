module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueGeneratesUnramifiedExtResidueField
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

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.residue_generates_unramifiedExt_residueField : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A), (∀ e, ψ (φ e) = algebraMap K.E B.A e) → Nontrivial B.A → (∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) → ∀ (s : K'.O) (Q : K'.O[X]), Q.Monic → Q.eval₂ (ψ.comp (algebraMap K'.O K'.E)) B.g = 0 → Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree → ∀ y : K'.O, ∃ f : K.O[X], ∃ z ∈ IsLocalRing.maximalIdeal K'.O, algebraMap K'.O K'.E y = f.eval₂ (φ.comp (algebraMap K.O K.E)) (algebraMap K'.O K'.E s) + algebraMap K'.O K'.E z := by
  first | exact @GlobalTheory.UnitLemma.Unr.residue_generates | exact GlobalTheory.UnitLemma.Unr.residue_generates | (intros; apply GlobalTheory.UnitLemma.Unr.residue_generates <;> assumption)
