module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLeviParabolicFormula
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

theorem _root_.GlobalTheory.T.constant_term_levi_parabolic_formula : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (φ : Sm E (r + s)), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ.1 (ratGL E (r + s) γ * g) = φ.1 g) → IsOpen {k | finRep E (r + s) k φ = φ} → ∀ [MeasurableSpace (BlockIx (r + s) r → Ad E)] [BorelSpace (BlockIx (r + s) r → Ad E)] (μ : Measure (BlockIx (r + s) r → Ad E)) (𝓕 : Set (BlockIx (r + s) r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E (r + s) r) 𝓕 μ → ∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)), ∫ x in 𝓕, φ.1 (unip x * (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.integral_unip_lev_mul | exact GlobalTheory.CompanionTheory.CTFin.integral_unip_lev_mul | (intros; apply GlobalTheory.CompanionTheory.CTFin.integral_unip_lev_mul <;> assumption)
