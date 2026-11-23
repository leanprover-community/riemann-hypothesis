module

import Development.WeilBound.CoreStatements.HodgeTatePoints.MlLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsInGenericFibre

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.M0
open scoped CategoryTheory.Obj
namespace GenericFibreProof

theorem spMap_field_pt {R K : Type} [CommRing R] [Field K] (δ : R →+* K) (z : Sp K) :
    (spMap δ z).asIdeal = RingHom.ker δ := by
  have hz : z.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := z.2)
  show Ideal.comap δ z.asIdeal = _
  rw [hz]; rfl

theorem preimm_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) : IsPreimmersion (spMap β) := by
  letI := β.toAlgebra
  haveI := h
  exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)

theorem generic_max {X : Type} [TopologicalSpace X] [T0Space X] {v v' : X} (h : v ∈ genericPoints X)
    (hs : v' ⤳ v) : v' = v := by
  have h1 : closure {v} ⊆ closure {v'} := specializes_iff_closure_subset.1 hs
  have h2 : closure {v'} ⊆ closure {v} := h.2 isIrreducible_singleton.closure h1
  exact (hs.antisymm (specializes_iff_closure_subset.2 h2)).eq

theorem mem_of_dense_of_max {X : Type} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {U : Set X} (ho : IsOpen U) (hd : Dense U) {z : X} (hz : ∀ z', z' ⤳ z → z' = z) : z ∈ U := by
  have hC := irreducibleComponent_mem_irreducibleComponents z
  obtain ⟨o, hoo, ⟨u, hu⟩, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨w, hwo, hwU⟩ := hd.inter_open_nonempty o hoo ⟨u, hu⟩
  have hg := hC.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents _ hC).closure_eq] at hg
  have hgz : hC.1.genericPoint = z := hz _ (hg.specializes mem_irreducibleComponent)
  have hzw : z ⤳ w := hgz ▸ hg.specializes (hoC hwo)
  exact hzw.mem_open ho hwU

private theorem isLocallyNoetherian_of_closedImmersion_pSpace (O F : Type) [CommRing O] [Field F] (β : O →+* F) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (hp : IsProjOver s) : TopologicalSpace.NoetherianSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) := by
  obtain ⟨N, i, hi, hs⟩ := hp
  haveI := hi
  haveI : Algebra.FiniteType ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)
      (MvPolynomial (Fin (N + 1)) O) :=
    haveI : IsScalarTower O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)
        (MvPolynomial (Fin (N + 1)) O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  have hsurj : Function.Surjective
      (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)) := by
    rintro ⟨p, hp⟩
    have h0 : p.totalDegree = 0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := p)).mpr
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0).symm
  haveI : LocallyOfFiniteType (spMap (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0))) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ hsurj
  haveI : LocallyOfFiniteType (PSpace.str O N) := by
    unfold PSpace.str
    infer_instance
  haveI : QuasiCompact (PSpace.str O N) := by
    unfold PSpace.str
    infer_instance
  haveI : LocallyOfFiniteType s := by
    rw [← hs]
    infer_instance
  haveI : QuasiCompact s := by
    rw [← hs]
    infer_instance
  haveI : IsLocallyNoetherian (pullback s (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β))
  haveI : CompactSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (spMap β))
  haveI : IsNoetherian (pullback s (spMap β)) := {}
  infer_instance

theorem generic_points_range_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j := by
  apply PositivityTheory.HtPt.Ml.generic_points_range <;> assumption

end GenericFibreProof


theorem _root_.GlobalTheory.T.generic_points_in_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j := by
  exact @GenericFibreProof.generic_points_range_local
