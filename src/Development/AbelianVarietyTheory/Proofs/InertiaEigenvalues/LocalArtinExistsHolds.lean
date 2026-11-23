module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalArtinExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInverseLocalArtinWeilGroupHomStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinReciprocityMapUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseLocalArtinContinuousOnInertiaStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmoothWeilCharEqOneOfToAbsGaloisAbEqOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem LocLanglands.isSmoothChar_of_comp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (hs : Function.Surjective a)
    (hc : Continuous fun σ : Ine (F := E) A => a (ineIncl h σ))
    (ho : ∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) {χ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : WeilDeligne.IsSmooth (χ.comp a)) : IsSmoothChar χ := by
  haveI : CompactSpace (Ine (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  have hK : IsOpen {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1} := hχ
  have hC : IsClosed ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ) :=
    (hK.isClosed_compl.isCompact.image hc).isClosed
  have hU : {x : (w.adicCompletion E)ˣ | valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1} ∈ nhds 1 := by
    have h1 : {x : w.adicCompletion E | valuation (w.adicCompletion E) (x - 1) < 1} ∈ nhds 1 := by
      rw [IsValuativeTopology.mem_nhds_iff]
      exact ⟨1, fun z hz => by simpa [neg_add_eq_sub] using hz⟩
    have h2 := Units.continuous_val.continuousAt (x := (1 : (w.adicCompletion E)ˣ)) h1
    refine Filter.mem_of_superset h2 fun x hx => ?_
    have h3 : valuation (w.adicCompletion E) ((x : w.adicCompletion E) - 1) < 1 := hx
    have := Valuation.map_one_add_of_lt _ h3
    simpa using this
  refine Subgroup.isOpen_of_mem_nhds χ.ker (g := 1) ?_
  have h1 : (1 : (w.adicCompletion E)ˣ) ∈ ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ)ᶜ := by
    rintro ⟨σ, hσ, e⟩
    refine hσ ?_
    have e' : a (ineIncl h σ) = 1 := e
    simp [e']
  refine Filter.mem_of_superset (Filter.inter_mem hU (hC.isOpen_compl.mem_nhds h1)) ?_
  rintro x ⟨hx, hx'⟩
  obtain ⟨σ, rfl⟩ := hs x
  have h0 : deg σ = 0 := by
    have := ho σ
    rw [ord_eq_zero_iff.2 hx] at this
    omega
  by_contra hn
  exact hx' ⟨⟨σ, deg_eq_zero_iff.mp h0⟩, hn, rfl⟩

theorem localArtinExists_holds : LocalArtinExists := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨art, hart⟩ := globalArtinReciprocity_holds E Ω
  obtain ⟨a, hs, ho, hg⟩ := T.exists_inverse_localArtin_weilGroup_hom E Ω A w h art hart
  have hc := T.inverseLocalArtin_continuousOn_inertia E Ω A w h art a hart ho hg
  refine ⟨a, hs, hc, ho, fun ξ hξ => ?_, fun art' hart' => ?_⟩
  · have hker : a.ker ≤ ξ.ker := fun σ hσ => by
      refine T.smoothWeilChar_eq_one_of_toAbsGaloisAb_eq_one E Ω A w h ξ hξ σ ?_
      rw [← hg σ, MonoidHom.mem_ker.1 hσ, map_one, map_one]
    have e : ξ = (a.liftOfSurjective hs ⟨ξ, hker⟩).comp a :=
      (MonoidHom.liftOfRightInverse_comp a _ (Function.rightInverse_surjInv hs) ⟨ξ, hker⟩).symm
    exact ⟨_, isSmoothChar_of_comp hs hc ho (e ▸ hξ), e⟩
  · rw [T.globalArtinReciprocityMap_unique E Ω art' art hart' hart]
    exact hg

end GlobalTheory
