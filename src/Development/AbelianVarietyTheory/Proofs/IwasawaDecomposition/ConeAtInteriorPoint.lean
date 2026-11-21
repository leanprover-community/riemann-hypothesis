import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteLocalEtaleNeighbourhood
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianPolarized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_local_etale_neighbourhood : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (s : X ⟶ Sp F), LocallyOfFiniteType s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ x : X, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (ξ : Sp R ⟶ X), IsCN R ∧ ξ (closedPoint R) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧ ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified ∧ ∀ p, ξ p ⤳ x := by
  first | exact @GlobalTheory.GenFan.exists_chart | exact GlobalTheory.GenFan.exists_chart | (intros; apply GlobalTheory.GenFan.exists_chart <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semi_abelian_polarized : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X), IsCN R → Set.range ξ ⊆ Set.range Y.j → ∃ (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), PolAt t (jK R) ∧ ThetaNZ t.G t.PP.L ∧ ∀ x, x ∈ abLocus t.G := by
  first | exact @GlobalTheory.GenFan.Tri.exists_sab | exact GlobalTheory.GenFan.Tri.exists_sab | (intros; apply GlobalTheory.GenFan.Tri.exists_sab <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem exists_pelUnif_torsionIso_subsingleton_of_abLocus {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (hR : IsCN R) (hpol : PolAt t (jK R))
    (hth : ThetaNZ t.G t.PP.L) (hab : ∀ x, x ∈ abLocus t.G) :
    ∃ P : PELUnif (maximalIdeal R) t, P.TorsionIso ∧ Subsingleton P.D.toPre.X := by
  obtain ⟨hn, hi, hc, hz⟩ := hR
  obtain ⟨l1, l2, l3, l4, l5, -⟩ := GlobalTheory.allSixLaws
  have hadm := GlobalTheory.isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hn hi hc
  have hpir : IsPrincipalIdealRing (R ⧸ maximalIdeal R) := by
    letI := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  obtain ⟨P, hP⟩ := LN.UnifPrime.exists_pelUnif l1 l2 l3 l4 l5 LN.ega_holds uniformisation_dvr_unconditional
    LN.pelSt_holds E H R _ hadm hpir t hpol (GoodTrait.splitOver_of_abLocus t.G t.semi hab) hth
  refine ⟨P, hP, ?_⟩
  have hmax : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ maximalIdeal R ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (R ⧸ maximalIdeal R ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (CartesianMonoidalCategory.toUnit_unique _ _)⟩
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick R (maximalIdeal R) 0) p (hab _)
    P.D.toPre.X g.i g.i_hom

end GlobalTheory.GenFan
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformization_abelian : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)), IsCN R → PolAt t (jK R) → ThetaNZ t.G t.PP.L → (∀ x, x ∈ abLocus t.G) → ∃ P : PELUnif (maximalIdeal R) t, P.TorsionIso ∧ Subsingleton P.D.toPre.X := by
  first | exact @GlobalTheory.GenFan.exists_pelUnif_torsionIso_subsingleton_of_abLocus | exact GlobalTheory.GenFan.exists_pelUnif_torsionIso_subsingleton_of_abLocus | (intros; apply GlobalTheory.GenFan.exists_pelUnif_torsionIso_subsingleton_of_abLocus <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

section Empty

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isCone_empty (H : Host E) (φ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Subsingleton X] : ConeO H φ X 0 Fin.elim0 := by
  have hB : ∀ β : LinearMap.BilinForm ℤ X, β = 0 := fun β =>
    LinearMap.ext₂ fun a b => by rw [Subsingleton.elim a 0]; simp
  have hz : ∀ β : LinearMap.BilinForm ℤ X, φ.evalZ β = 0 := fun β => φ.eval_of_subsingleton _
  refine ⟨fun i => i.elim0, fun i => i.elim0, ?_, fun c _ => ?_, ?_⟩
  · have : Subsingleton (balForms H.bar X) := ⟨fun a b => Subtype.ext ((hB a).trans (hB b).symm)⟩
    exact ⟨0, Module.Basis.empty _, fun i => i.elim0⟩
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact φ.eval_of_subsingleton _
  · refine ⟨1, 0, one_pos, fun i => i.elim0, fun β _ _ => by simp [hz], fun β _ _ _ => ⟨1, Fin.elim0, one_pos, ?_⟩⟩
    simp [hB β]

theorem inCone_empty {R : Type} [CommRing R] [IsDomain R] (Dg : DegPre R) [Subsingleton Dg.X] :
    InCone Dg (m := 0) Fin.elim0 := by
  intro W _ _ _ _ ϖ _ f be _ _
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  ext a b
  rw [Subsingleton.elim a 0]
  simp

end Empty

end GlobalTheory.GenFan

namespace GlobalTheory.GenFan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem isOpenImmersion_j (Y : Model Xo c (RingHom.id c.F)) : IsOpenImmersion Y.j := by
  unfold Model.j
  have : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
      infer_instance
    infer_instance
  have := Y.jQ_open
  infer_instance

theorem coneAt_j (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (w : Xo.XF c) :
    GlobalTheory.GenFan.ConeAt (ConeO H φ) Y (Y.j w) := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsProper Y.s := projProper _ _ _ Y.proj
  obtain ⟨R, _, _, _, ξ, hR, hξ, he, hu, hsp⟩ := GlobalTheory.T.exists_complete_local_etale_neighbourhood c.F Y.X Y.s inferInstance Y.normal (Y.j w)
  have hj := isOpenImmersion_j Y
  have hr : Set.range ξ ⊆ Set.range Y.j := fun _ ⟨p, hp⟩ =>
    hp ▸ (hsp p).mem_open Y.j.isOpenEmbedding.isOpen_range ⟨w, rfl⟩
  obtain ⟨t, m, hpol, hth, hab⟩ := GlobalTheory.T.exists_semi_abelian_polarized Y R ξ hR hr
  obtain ⟨P, hP, hX⟩ := GlobalTheory.T.exists_uniformization_abelian R t hR hpol hth hab
  exact ⟨R, _, _, _, ξ, t, m, P, 0, Fin.elim0, hR, hξ, he, hu, hP, isCone_empty H φ _, inCone_empty _⟩

end GlobalTheory.GenFan
end
end
