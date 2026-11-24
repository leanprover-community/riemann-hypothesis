module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealFrameAutomorphismUnitriangularRowsCoords
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.T.realFrame_automorphism_unitriangular_rows_coords : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → (∀ (i : UTin β) (u : Fin r → K), s (N.F.e i.1.1.2.castSucc) = N.F.e i.1.1.2.castSucc + ∑ c, u c • N.F.e c.castSucc → q.1 i = ((ρ ^ (i.1.1.2.val - i.1.1.1.val) : ℝ) : ℂ) * σ (u i.1.1.1)) ∧ (q.1 = 0 → ∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ (q.1 = 0 → ∀ (b : {a : Fin r // N.j ≤ a.val}) (y : V), s (N.ist b.1) - N.ist b.1 - y ∈ II N.F N.F' → q.2.1 b = ((ρ ^ (r - b.1.val) : ℝ) : ℂ) • fun l => Φ y (wI k r l)) := by
  first | exact @GlobalTheory.DegVol.RefCovTop.coords_top | exact GlobalTheory.DegVol.RefCovTop.coords_top | (intros; apply GlobalTheory.DegVol.RefCovTop.coords_top <;> assumption)
