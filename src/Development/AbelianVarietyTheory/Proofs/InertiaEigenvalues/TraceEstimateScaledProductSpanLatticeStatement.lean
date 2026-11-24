module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TupMemLatT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceEstimateScaledProductSpanLattice
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.trace_estimate_scaledProductSpanLattice : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (c N n : ℕ) (cs : Fin m → Om l), n ≤ N → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∃ M₁ : ℕ, ∀ M, M₁ ≤ M → ∀ (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ GlobalTheory.TraceConjugationCover.latL t M → ‖(F.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace - ∑ k, cs k * (((F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y) k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  first | (exact @GlobalTheory.trace_estimate_latL) | (exact GlobalTheory.trace_estimate_latL) | (intros; apply GlobalTheory.trace_estimate_latL  <;> assumption)
