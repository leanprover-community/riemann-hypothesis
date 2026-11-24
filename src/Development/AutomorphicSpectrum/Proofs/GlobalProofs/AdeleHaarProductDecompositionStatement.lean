module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdeleHaarProductDecomposition
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
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsCovolOne

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix


theorem _root_.GlobalTheory.T.adele_haar_product_decomposition : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (m : Measure (ι → AF F)) (μ₁ : Measure (ι → Ainf F)) (μ₂ : Measure (ι → Af F)), m.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ m.map (fun y : ι → AF F => ((fun i => (y i).1, fun i => (y i).2) : (ι → Ainf F) × (ι → Af F))) = c • μ₁.prod μ₂ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod <;> assumption)
