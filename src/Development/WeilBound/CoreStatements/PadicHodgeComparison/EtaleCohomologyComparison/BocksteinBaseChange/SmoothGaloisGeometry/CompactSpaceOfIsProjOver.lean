module

import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SpecOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison

namespace GeoD


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isProper_pspace (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  apply _root_.UpperTheory.Gal.Seam.Spec.isProper_pstr <;> assumption

theorem compactSpace_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_pspace R N
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R N)

end GeoD

theorem geoMain : GeometricGenericComponents := by
  intro l _ K M hM d hC
  obtain ⟨hconn, hsm⟩ := hC
  have : Smooth M.q := SmoothOfRelativeDimension.smooth d M.q
  have : CompactSpace M.X := GeoD.compactSpace_of_isProjOver hM.1
  have : QuasiCompact M.p := quasiCompact_of_compactSpace M.p
  have : CompactSpace M.gen := inferInstance
  obtain ⟨r, U, hint, hcov, hdisj, hperm, htrans⟩ := GeoC.exists_components (Ω := PadicAlgCl l) M.q
  have hne : ∀ s, (U s : Set (GlobalTheory.Et.geom (PadicAlgCl l) M.q)).Nonempty := fun s => by
    obtain ⟨⟨y, hy⟩⟩ := (hint s).nonempty
    exact ⟨y, hy⟩
  refine ⟨r, fun s => (U s).toScheme, fun s => (U s).ι, ⟨fun s => inferInstance, fun y => ?_, fun s s' h => ?_⟩,
    hint, fun σ => ?_, fun s s' => ?_⟩
  · obtain ⟨s, hs⟩ := hcov y
    exact ⟨s, by rw [Scheme.Opens.range_ι]; exact hs⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact hdisj s s' h
  · set g := GlobalTheory.Et.galMap (PadicAlgCl l) M.q (IntermediateField.fixingSubgroupEquiv K σ)
    choose f hf using hperm (IntermediateField.fixingSubgroupEquiv K σ)
    have hginj : Function.Injective g := (GeoC.galHomeo M.q (IntermediateField.fixingSubgroupEquiv K σ)).injective
    have hinj : Function.Injective f := by
      intro s s' hss'
      by_contra h
      have h1 : (U s : Set _) = U s' :=
        Set.image_injective.2 hginj ((hf s).trans (hss' ▸ (hf s').symm))
      obtain ⟨y, hy⟩ := hne s
      exact Set.disjoint_left.1 (hdisj s s' h) hy (h1 ▸ hy)
    let π := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
    have hr : ∀ s, Set.range ((U s).ι ≫ g) = Set.range (U (π s)).ι := fun s => by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact hf s
    exact ⟨π, fun s => IsOpenImmersion.isoOfRangeEq ((U s).ι ≫ g) (U (π s)).ι (hr s),
      fun s => (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩
  · obtain ⟨τ, hτ⟩ := htrans s s'
    refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm τ, ?_⟩
    rw [MulEquiv.apply_symm_apply]
    have hr : Set.range ((U s).ι ≫ GlobalTheory.Et.galMap (PadicAlgCl l) M.q τ) = Set.range (U s').ι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact hτ
    exact ⟨(IsOpenImmersion.isoOfRangeEq _ _ hr).hom, (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm⟩

end CrystallineSemistableComparison
