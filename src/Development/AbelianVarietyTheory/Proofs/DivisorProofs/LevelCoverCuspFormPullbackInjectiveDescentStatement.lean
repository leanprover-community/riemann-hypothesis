module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverCuspFormPullbackInjectiveDescent
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

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c' 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → (letI : Algebra c.F d.c₂.F := ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle)).toAlgebra; IsGalois c.F d.c₂.F) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∃ π : cuspW Xo c U (wtZ a n) →ₛₗ[((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))] cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), (∀ f : cuspW Xo c U (wtZ a n), Pull d (rulBC hle (f : Rul Xo c)) (π f : Rul d.Xo₂ d.c₂)) ∧ (∀ (m : ℕ) (b : Fin m → cuspW Xo c U (wtZ a n)), LinearIndependent c.F b → LinearIndependent d.c₂.F (fun k => π (b k))) ∧ (∀ (σ₂ : d.c₂.F →+* ℂ) (f : cuspW Xo c U (wtZ a n)), normW U₂ (xiR D) (fun _ => D.sp.W j) dict₂ (wtZ a n) σ₂ (π f) = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF c c' hle))) f) ∧ (∀ f : cuspW Xo c U (wtZ a n), π f ∈ latW U₂ (wtZ a n) ↔ f ∈ latW U (wtZ a n)) ∧ (∀ g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (Set.range π) ↔ FibConst d (g : Rul d.Xo₂ d.c₂)) ∧ ∀ (C : Submodule c.F (cuspW Xo c U (wtZ a n))), ∀ δ ∈ differentIdeal ℤ (𝓞 d.c₂.F), ∀ g ∈ latW U₂ (wtZ a n), g ∈ Submodule.span d.c₂.F (π '' (C : Set (cuspW Xo c U (wtZ a n)))) → δ • g ∈ Submodule.span (𝓞 d.c₂.F) (π '' {f | f ∈ C ∧ f ∈ latW U (wtZ a n)}) := by
  first | exact @GlobalTheory.LevRingDesc.levRing_descent | exact GlobalTheory.LevRingDesc.levRing_descent | (intros; apply GlobalTheory.LevRingDesc.levRing_descent <;> assumption)
