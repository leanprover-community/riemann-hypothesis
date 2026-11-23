module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterRecCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRecCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantRecCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LFactorRecCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistRecCompatibleStatement
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

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isRec_of_isRecLit : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecLit h rc → IsRec h rc := by
  intro hDZ hDI hEx hLM hSC hZP hGL hBZ E Ω _ _ _ _ _ A w h rc H
  obtain ⟨a, ha, ε, hε, L⟩ := H
  refine ⟨a, ha, ε, hε, ?_⟩
  exact
    { bij := L.bij, dim := L.dim, one := L.one, eps := L.eps, cusp := L.cusp, langlands := L.langlands,
      twist := L.twist, central := L.central, dual := L.dual,
      det := GlobalTheory.T.determinant_rec_compatible hSC E Ω A w h a ha _ rc L
      prod := GlobalTheory.T.twist_rec_compatible hEx hLM hSC E Ω A w h a ha _ rc L
      supp := GlobalTheory.T.central_character_rec_compatible hEx hZP hGL hBZ E Ω A w h a ha _ rc L
      sph := GlobalTheory.T.l_factor_rec_compatible hEx hLM hSC hZP hGL hBZ E Ω A w h a ha _ rc L
      sat := GlobalTheory.T.epsilon_factor_rec_compatible hEx hLM hSC hZP hGL hBZ E Ω A w h a ha _ rc L
      depth := GlobalTheory.T.conductor_rec_compatible hDZ hDI hEx hZP hGL hBZ E Ω A w h rc ⟨a, ha, ε, hε, L⟩ }

end GlobalTheory.LocLanglands
