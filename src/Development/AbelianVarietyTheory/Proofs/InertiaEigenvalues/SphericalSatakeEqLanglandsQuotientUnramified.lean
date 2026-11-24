module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotientStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationSupercuspidalSupportMultiStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSegmentRepLengthOneUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotientStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGLStatement
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.SatakeL

theorem isL_single_unrChar : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL →
    ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (x : IrrGL (k := k)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α →
      IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (GlobalTheory.SmGL.unrChar k (α i))
        (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  intro hEx hLM hSC hZP hGL hBZ k _ _ _ _ _ x α hsat
  obtain ⟨𝔪, hL⟩ := hEx k x
  obtain ⟨h, y, hd, ⟨Δ, hord, hseg⟩, hcos⟩ := id hL

  have hsphy : ∀ a, IsSpherical (y a).rep :=
    GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k h x.1 y hd x.2.rep.V x.rep hcos.isSubquotient hsat.2.1

  have hlen : ∀ i, (Δ i).len = 1 := fun i =>
    (GlobalTheory.T.sphericalSegmentRep_length_one_unramified hLM hSC hZP hGL hBZ k (Δ i) (y i) (hseg i) (hsphy i)).1
  have hsingle : ∀ i, Δ i = Segment.single (Δ i).first (Δ i).isCusp_first := fun i =>
    Segment.ext_first rfl (by rw [hlen i]; rfl)
  have hms : ∀ i, (Δ i).ms = {(Δ i).first} := fun i =>
    (congrArg Segment.ms (hsingle i)).trans (Segment.ms_single _ _)

  have h1 : HasSupport x.rep (msupp 𝔪) := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZP k 𝔪 x hL
  have h2 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => GlobalTheory.SmGL.unrChar k (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) x.2.rep hsat.2.2
  have heq := GlobalTheory.T.supercuspidalSupport_unique_GL hGL hBZ hZP k x _ _ h1 h2
  have hsupp : msupp 𝔪 = Finset.univ.val.map fun i => (Δ i).first := by
    rw [msupp, ← hord.1, Multiset.bind_map]
    simp only [hms]
    exact Multiset.bind_singleton _ _
  rw [hsupp] at heq

  have hinj : Function.Injective fun D : Segment k => (D.first, D.len) := fun a b e =>
    Segment.ext_first (congrArg Prod.fst e) (congrArg Prod.snd e)
  have hm : 𝔪 = Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (GlobalTheory.SmGL.unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _) := by
    apply Multiset.map_injective hinj
    have e1 := congrArg (Multiset.map fun ρ : IrrGL (k := k) => (ρ, 1)) heq
    simp only [Multiset.map_map, Function.comp_def] at e1
    rw [← hord.1, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, hlen]
    exact e1
  rw [← hm]
  exact hL

end GlobalTheory.LocLanglands.SatakeL
