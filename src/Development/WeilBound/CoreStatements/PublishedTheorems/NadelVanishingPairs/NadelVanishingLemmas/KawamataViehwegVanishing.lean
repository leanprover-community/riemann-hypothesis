module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassCanonicalBundleBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfCechPicardClassEqStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfRelSncDivisorStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegSpreadingStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SpreadOutRelativeSncStatement
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair

namespace GlobalTheory.Div

theorem vanishing_ample_snc_charZero : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) (f : X ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d f], IsProjOver f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : RelSnc f d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • cls (L i) (h.isLB i) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  intro k _ _ X f d _ hproj s L σ h K M A hM hA r b hr hb hcls q hq
  have hprop : IsProper f := GlobalTheory.SchemeWords.isProper_of_isProjOver hproj
  obtain ⟨R, X₁, f₁, π, L₁, σ₁, h₁, M₁, hM₁, hft, hprop₁, hpb, hL, hMc⟩ :=
    GlobalTheory.T.spread_out_relative_snc k X f d hprop s L σ h M hM
  haveI : SmoothOfRelativeDimension d f₁ := GlobalTheory.T.smoothOfRelativeDimension_of_relSncDivisor R X₁ f₁ d s L₁ σ₁ h₁
  haveI : IsProper f₁ := hprop₁
  obtain ⟨K₁⟩ := (CanonLB.nonempty : Nonempty (CanonLB f₁ d))
  obtain ⟨A₁, hA₁, hA₁c⟩ := cls_surj (r • cls M₁ hM₁ - r • cls K₁.bundle K₁.isLB -
    ∑ i, b i • cls (L₁ i) (h₁.isLB i))
  have hK : cls K.bundle K.isLB = CechPic.pull π (cls K₁.bundle K₁.isLB) :=
    GlobalTheory.T.cechPicardClass_canonicalBundle_baseChange R k R.subtype X₁ X f₁ f π d K₁ K hpb
  have hApull : cls (A₁.pull π) (pull_isLB hA₁ π) = cls A hA.isLB := by
    have e : cls A hA.isLB = r • cls M hM - r • cls K.bundle K.isLB - ∑ i, b i • cls (L i) (h.isLB i) := by
      rw [hcls]; abel

    rw [e, cls_pull hA₁, hA₁c, map_sub, map_sub, map_nsmul, map_nsmul, map_sum, ← hMc, ← hK]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, ← hL i]
  have hAamp : IsAmpleLB (A₁.pull π) :=
    IsAmpleLB.of_lbIso hA (pull_isLB hA₁ π) ((cls_eq_iff _ _).1 hApull)
  have hcls₁ : r • cls M₁ hM₁ = r • cls K₁.bundle K₁.isLB + ∑ i, b i • cls (L₁ i) (h₁.isLB i) +
      cls A₁ hA₁ := by
    rw [hA₁c]; abel
  have hv := GlobalTheory.T.kawamata_viehweg_spreading R k R.subtype X₁ X f₁ f π d hft Subtype.coe_injective hpb s L₁ σ₁ h₁ K₁
    M₁ A₁ hM₁ hA₁ r b hAamp hr hb hcls₁ q hq
  have hMM : cls (M₁.pull π) (pull_isLB hM₁ π) = cls M hM := by rw [cls_pull hM₁, hMc]
  exact GlobalTheory.T.cohomology_subsingleton_of_cechPicardClass_eq X (M₁.pull π) M _ hM hMM q hv

end GlobalTheory.Div
