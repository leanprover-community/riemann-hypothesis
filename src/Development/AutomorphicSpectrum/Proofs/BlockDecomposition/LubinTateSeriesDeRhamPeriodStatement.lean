module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSeriesDeRhamPeriod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Reciprocity

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical


theorem _root_.GlobalTheory.T.lubin_tate_series_de_rham_period : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (π : ↥(OL K)) (S : Subring (Formalism.Per6.BdRp l)),
    (∀ a, wB l a ∈ S) → (∀ c, oB K μ c ∈ S) → PerEnv S (FB l) (oB K μ π) → π ∣ (l : ↥(OL K)) →
    ∀ (r : ↥(OL K) →+* Tl l), (∀ c, ∃ c', tch l (r c) = oB K μ (c + π * c')) →
    ∀ (x y : Tl l), ‖thB l (tch l x)‖ < 1 → ∀ (φ : PowerSeries ↥(OL K)),
      (∀ D, x ^ D ∣ y - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i) →
      EvalMod S (FB l) (oB K μ π) (oB K μ) φ (tch l x) (tch l y) 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Glue.evalMod_teichmuller | exact GlobalTheory.CompanionTheory.LTPer.Glue.evalMod_teichmuller | (intros; apply GlobalTheory.CompanionTheory.LTPer.Glue.evalMod_teichmuller <;> assumption)
