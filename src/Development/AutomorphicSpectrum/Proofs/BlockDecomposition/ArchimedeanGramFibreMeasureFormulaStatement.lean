module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanGramFibreMeasureFormula
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.archimedean_gram_fibre_measure_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∀ minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ c : HermR (Ainf F) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, IsSchwartzArch φ → Measurable φ ∧ (∀ᶠ s in nhds c, Integrable φ (minf s)) ∧ ContinuousAt (fun s => ∫ X, φ X ∂(minf s)) c := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.FibN.fibre_schwartzN | exact GlobalTheory.CompanionTheory.SiegelND.Coef.FibN.fibre_schwartzN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.FibN.fibre_schwartzN <;> assumption)
