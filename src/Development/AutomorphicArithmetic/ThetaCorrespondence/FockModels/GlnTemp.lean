module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TemperedProductOfSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnSuff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTCentred
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.GlnTOrderfree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCosocleUnit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TProdExp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFreeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissibleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableUnitarizableStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedLanglandsFactorsSquareIntegrableStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSegmentRepresentationStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Development
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace UpperTheory.Lit.Cas

theorem temperedProduct (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hE : GlobalTheory.Published.LanglandsExhaustionGL) (hC : GlobalTheory.Published.StandardCosocleGL) (hM : GlobalTheory.Published.LanglandsMultisegments)
    (hS : GlobalTheory.Published.EssSquareIntegrableSegments) : GlobalTheory.Published.TemperedProductOfSquareIntegrable := by
  intro k _ _ _ _ _ N hN V _ _ π hs hi
  constructor
  · intro ht
    have hO : Zc.LOrderFree k := orderfree hC hM k
    have hSo : Zc.LSocleGL k := GlobalTheory.T.langlands_socle_of_order_free hA (GlobalTheory.T.local_langlands_of_irreducible_admissible hA) hO
    have hL : Zc.LSegExists k := fun Δ => GlobalTheory.TL.exists_segment_representation hA Δ
    obtain ⟨𝔪, h𝔪⟩ := hE k (IrrGL.of π hs hi)
    have h𝔪' : IsL 𝔪 π := h𝔪.of_equiv (IrrGL.equivOf π hs hi).symm
    obtain ⟨h, x, hd, hx, hu⟩ := GlobalTheory.T.tempered_langlands_factors_square_integrable k hSo (Zl.JC.casselmanNecTemp_holds k) hL 𝔪 N π hN hs hi ht h𝔪'
    obtain ⟨Δ, hΔo, hΔ⟩ := hx
    have hsq : ∀ a, IsSqIntCoeff (x a).rep := fun a => centred hS hA k (Δ a) (x a) (hΔ a) (hu a)
    have e := cosocleUnit hBZ k h N x hd V π (fun a => GlobalTheory.T.square_integrable_unitarizable k (x a) (hsq a)) (hO 𝔪 h N x hd ⟨Δ, hΔo, hΔ⟩ π h𝔪')
    refine ⟨h, x, hd, fun a => ⟨?_, hsq a⟩, e⟩
    have h1 := (hΔ a).deg_eq
    have h2 := Nat.mul_pos (Δ a).len_pos (Δ a).d_pos
    simp only [Segment.deg] at h1
    omega
  · rintro ⟨h, δ, hd, hδ, e⟩
    obtain ⟨hu, hw⟩ := prodExp hG hBZ hA k (Zl.JC.casselmanNecSq_holds k) h N δ hd hδ V π hi e
    have H := casselmanSuffTemp hA hF k N π hN hs hi hu hw
    intro ε hε
    exact H ε hε

end UpperTheory.Lit.Cas

end
