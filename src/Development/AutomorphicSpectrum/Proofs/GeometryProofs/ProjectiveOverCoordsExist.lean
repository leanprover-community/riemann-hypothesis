module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsClopenSpecializationsGenPt
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MfCoords
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MfBase

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
private theorem isLocallyNoetherian_of_closedImmersion_pSpace (o : Type) [CommRing o] [IsNoetherianRing o] (X : Scheme.{0}) (N : ℕ)
    (i : X ⟶ PSpace o N) [IsClosedImmersion i] : IsLocallyNoetherian X := by
  refine isLocallyNoetherian_of_affine_cover
    (S := fun j : Fin (N + 1) => ⟨i ⁻¹ᵁ GlobalTheory.ProjSpace.chart o N j,
      (GlobalTheory.ProjSpace.isAffineOpen_chart o N j).preimage i⟩) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    have hx : i x ∈ (⨆ j, GlobalTheory.ProjSpace.chart o N j) := by
      rw [GlobalTheory.ProjSpace.iSup_chart]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩
  · intro j
    letI := GlobalTheory.ProjSpace.algebraSections o N (GlobalTheory.ProjSpace.chart o N j)
    haveI : IsNoetherianRing Γ(PSpace o N, GlobalTheory.ProjSpace.chart o N j) :=
      isNoetherianRing_of_ringEquiv _ (GlobalTheory.ProjSpace.chartAlgEquiv o N j).toRingEquiv
    exact isNoetherianRing_of_surjective _ _ (i.app (GlobalTheory.ProjSpace.chart o N j)).hom
      (Scheme.Hom.app_surjective i _ (GlobalTheory.ProjSpace.isAffineOpen_chart o N j))


theorem _root_.GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (X : Scheme.{0}) (s : X ⟶ Sp o), IsProjOver s → ∀ (Ω : Type) [Field Ω] [Algebra o Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ξ ≫ s = spMap (algebraMap o Ω) → ∃ (n : ℕ) (x : Fin n → Ω), CoordTie o ξ x := by
  intro o _ _ X s hs Ω _ _ ξ hξ hcomp
  obtain ⟨N, i, hi, rfl⟩ := hs
  haveI := isLocallyNoetherian_of_closedImmersion_pSpace o X N i
  have hZ := GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes X Ω ξ hξ
  let U : X.Opens := ⟨{q | genPt ξ ⤳ q}, hZ.isOpen⟩
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : y = closedPoint Ω := Subsingleton.elim _ _
    subst this
    exact specializes_rfl
  let ξ' : Sp Ω ⟶ U := IsOpenImmersion.lift U.ι ξ hr
  have hfac : ξ' ≫ U.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _
    (by rw [Scheme.Opens.range_ι]; exact hZ.isClosed)
  have hξ2 : IsCptGen (ξ' ≫ U.ι) := by rw [hfac]; exact hξ
  have hgen' : IsCptGen ξ' := PositivityTheory.HtPt.Mf.isCptGen_of_comp ξ' U.ι hξ2
  have h1 : U.ι (genPt ξ') = genPt ξ := by
    change (ξ' ≫ U.ι) (closedPoint Ω) = ξ (closedPoint Ω)
    rw [hfac]
  have hall : ∀ q, genPt ξ' ⤳ q := by
    intro q
    rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff, h1]
    exact q.2
  obtain ⟨t, ht, heq⟩ := PositivityTheory.HtPt.Mf.exists_point (ξ' ≫ U.ι ≫ i)
    (by simpa [Category.assoc, reassoc_of% hfac] using hcomp)
  have hct : CoordTie o ξ' t := PositivityTheory.HtPt.Mf.coordTie_of_all (i := U.ι ≫ i) hgen' hall heq
  have h2 : genPt (ξ' ≫ U.ι) = genPt ξ := by rw [hfac]
  have hsurj : ∀ q : Cpt (ξ' ≫ U.ι), ∃ p : Cpt ξ', PositivityTheory.HtPt.Mf.push ξ' U.ι p = q := by
    intro q
    have hq : genPt ξ ⤳ q.1 := by
      rw [← h2]
      exact q.2
    exact ⟨⟨⟨q.1, hq⟩, hall _⟩, Subtype.ext rfl⟩
  have hfin := PositivityTheory.HtPt.Mf.coordTie_comp (o := o) U.ι hξ2 hsurj hct
  rw [hfac] at hfin
  exact ⟨N + 1, t, hfin⟩
