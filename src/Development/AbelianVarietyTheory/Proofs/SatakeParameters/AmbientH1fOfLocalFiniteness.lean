module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalH1fFiniteDimensionalStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataCrystallineAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualContinuousIntegralOverEnlargedCoeffStatement
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

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Pass

theorem ambient_h1f_of_local_finiteness : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (i : D.nd.Loc)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i),
    Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) →
    EmbeddingTypes.H1fFiniteRankTorsion (D := D) i ρ π dc := by
  intro hLF D i ρ π dc hc _ w hw _ C L2 _ n
  obtain ⟨⟨_, hdvr, hfr⟩, -⟩ := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  haveI := hdvr
  haveI := hfr
  have hcont := GlobalTheory.T.twistedDual_continuous_integral_over_enlarged_coeff D i w hw C.LL C.le ρ π hc
  have hfin := GlobalTheory.T.local_h1f_finite_dimensional hLF (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL D.R.r
    (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) hcont.1 hcont.2
  exact GlobalTheory.T.period_data_crystalline_admissible (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) L2 hfin n

end GlobalTheory.Pass
