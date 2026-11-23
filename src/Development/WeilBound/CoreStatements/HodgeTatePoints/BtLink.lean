module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace PositivityTheory.HtPt.Twexists

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tors ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem exists_torsion' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (T : Type) [CommGroup T] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ), 1 ≤ N → ∀ τ : T →* (Over.mk ((genPt R).hom ≫ x) ⟶ G), Function.Injective τ → (∀ t, τ t ^ N = 1) → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (a : FractionRing R →+* Ω) (g : Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x) ⟶ G), g ^ N = 1 → ∃ t, g.left = Spec.map (CommRingCat.ofHom a) ≫ (τ t).left) → ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (Γ.pt t).left ≫ i = (τ t).left := by
  intro R _ _ _ _ T _ S G _ hG x N hN τ hτ htor hsurj
  haveI : IsCommMonObj G := hG.comm
  have hBs : IsSemiAbelian ((Over.pullback x).obj G) :=
    { comm := by have := hG.comm; infer_instance
      smooth := by have := hG.smooth; show Smooth (pullback.snd G.hom x); infer_instance
      separated := by have := hG.separated; show IsSeparated (pullback.snd G.hom x); infer_instance
      quasiCompact := by have := hG.quasiCompact; show QuasiCompact (pullback.snd G.hom x); infer_instance
      geomConnected := by have := hG.geomConnected; show GeometricallyConnected (pullback.snd G.hom x); infer_instance
      fibres := fun Ω _ _ q => by
        obtain ⟨E⟩ := hG.fibres Ω (q ≫ x)
        let eM := (Functor.mapMonNatIso (Over.pullbackComp q x) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
        let e : (Over.pullback (q ≫ x)).obj G ≅ (Over.pullback q).obj ((Over.pullback x).obj G) :=
          (Mon.forget _).mapIso eM
        haveI : IsMonHom e.hom := by
          show IsMonHom eM.hom.hom
          infer_instance
        letI := E.grpB
        haveI := E.q_hom
        haveI := E.i_hom
        refine ⟨{
          X := E.X
          addCommGroup := E.addCommGroup
          free := E.free
          finite := E.finite
          B := E.B
          grpB := E.grpB
          isAbelian := E.isAbelian
          q := e.inv ≫ E.q
          q_hom := inferInstance
          q_flat := ?_
          q_surjective := ?_
          q_quasiCompact := ?_
          i := E.i ≫ e.hom
          i_hom := inferInstance
          isKernel := ?_ }⟩
        · rw [Over.comp_left]
          have := E.q_flat
          have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
          infer_instance
        · rw [Over.comp_left]
          have := E.q_surjective
          have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
          infer_instance
        · rw [Over.comp_left]
          have := E.q_quasiCompact
          have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv
          infer_instance
        · refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }
  haveI : IsCommMonObj ((Over.pullback x).obj G) := hBs.comm
  haveI : Smooth ((Over.pullback x).obj G).hom := hBs.smooth
  haveI : IsSeparated ((Over.pullback x).obj G).hom := hBs.separated
  haveI : QuasiCompact ((Over.pullback x).obj G).hom := hBs.quasiCompact
  obtain ⟨hfl, hqf⟩ :=
    GlobalTheory.SemiAbMulFlat.flat_and_locallyQuasiFinite_pow _ _ hBs N (by omega)
  haveI := hfl
  haveI := hqf
  have hP : IsPullback (pullback.fst (𝟙 ((Over.pullback x).obj G) ^ N) η)
      (toUnit (pullback (𝟙 ((Over.pullback x).obj G) ^ N) η))
      (𝟙 ((Over.pullback x).obj G) ^ N) η := by
    convert IsPullback.of_hasPullback (𝟙 ((Over.pullback x).obj G) ^ N) η using 1
    exact toUnit_unique _ _
  obtain ⟨hA, hAc, hj⟩ := GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_kernel_grp hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := GlobalTheory.CompanionTheory.Ar.BT.Tors.kernel_props hP
  haveI := h1
  haveI := h5
  have het := GlobalTheory.CompanionTheory.Ar.BT.Tors.kernel_base_etale (genPt R).hom hP
    (GlobalTheory.CompanionTheory.Ar.BT.Tors.isUnit_natCast_generic (R := R) hN)
  haveI : AlgebraicGeometry.IsReduced (genPt R).left :=
    (inferInstance : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have hred : AlgebraicGeometry.IsReduced
      (pullback (pullback (𝟙 ((Over.pullback x).obj G) ^ N) η).hom (genPt R).hom) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced
      (pullback.snd (pullback (𝟙 ((Over.pullback x).obj G) ^ N) η).hom (genPt R).hom)
  exact GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_of_kernel hP h1 h2 h3 h4 h5 hred τ hτ htor hsurj

end PositivityTheory.HtPt.Twexists
