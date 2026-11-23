module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
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
import Mathlib.Tactic.Linter.HaveILetI
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

namespace GlobalTheory.CompanionTheory.LTPer

theorem actB_prod_periods {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l) (s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l))
    (hs : ∀ μ, μ ∈ s) (ht : ∀ μ, PrePer K χ μ (t μ))
    (g : GQ l) (hg : g ∈ GK K) (hfix : ∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), g (μ x) = μ x) :
      actB g (∏ μ ∈ s, t μ) =
        algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * ∏ μ ∈ s, t μ := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  letI : Fintype (↥K.1 →ₐ[ℚ_[l]] Om l) := minpoly.AlgHom.fintype ℚ_[l] (↥K.1) (Om l)
  have hsu : s = Finset.univ := Finset.eq_univ_iff_forall.2 hs
  set y : ↥K.1 := ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) with hy
  have hn : algebraMap ℚ_[l] (Om l) (Algebra.norm ℚ_[l] y) = ∏ μ ∈ s, μ y := by
    rw [hsu]
    exact Algebra.norm_eq_prod_embeddings ℚ_[l] (Om l) y
  have hr : algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] y) = ∏ μ ∈ s, rB l (μ y) := by
    rw [← map_prod, ← hn]
    exact ((GroundTheory.PAdicHodge.algClToBdR l).commutes _).symm
  rw [map_prod, hr, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun μ _ => (ht μ).2.1 g hg (hfix μ)

end GlobalTheory.CompanionTheory.LTPer
