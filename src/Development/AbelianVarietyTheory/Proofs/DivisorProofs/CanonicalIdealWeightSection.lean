import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerIsoFlagTangentStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationKsIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationKsIsoSecStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_kodairaSpencer_identification_offBoundary : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → Nonempty (CanId M) := by
  first | exact @GlobalTheory.CompHS.canId_nonempty | exact GlobalTheory.CompHS.canId_nonempty | (intros; apply GlobalTheory.CompHS.canId_nonempty <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory

theorem dense_open_eq_top_of_smoothOfRelativeDimension_zero : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k), SmoothOfRelativeDimension 0 p → ∀ (U : Y.Opens), Dense (U : Set Y) → U = ⊤ := by
  intro k _ Y p hp U hU
  have he : Etale p := (Etale.iff_smoothOfRelativeDimension_zero p).2 hp
  have hq : LocallyQuasiFinite p := by
    refine ⟨fun {V} hV {W} hW e ↦ ?_⟩
    have h := p.etale_appLE hV hW e
    letI := (p.appLE V W e).hom.toAlgebra
    have : Algebra.Etale Γ(Sp k, V) Γ(Y, W) := h
    exact (inferInstance : Algebra.QuasiFinite Γ(Sp k, V) Γ(Y, W))
  have hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hopen : ∀ y : Y, IsOpen ({y} : Set Y) := by
    intro y
    have hd : _root_.IsDiscrete (p ⁻¹' {p y}) := p.isDiscrete_preimage_singleton (p y)
    have huniv : p ⁻¹' {p y} = Set.univ := by
      ext z; simp [Subsingleton.elim (p z) (p y)]
    rw [huniv] at hd
    have : DiscreteTopology Y := by
      have h2 := hd.to_subtype
      exact (Homeomorph.Set.univ Y).symm.isEmbedding.discreteTopology
    exact isOpen_discrete _
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨z, hz1, hz2⟩ := hU.inter_open_nonempty {y} (hopen y) ⟨y, rfl⟩
  rw [Set.mem_singleton_iff] at hz1
  subst hz1
  exact hz2

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_open_eq_univ_of_smooth_relDim_zero : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k), SmoothOfRelativeDimension 0 p → ∀ (U : Y.Opens), Dense (U : Set Y) → U = ⊤ := by
  atlas_forward_decl GlobalTheory.dense_open_eq_top_of_smoothOfRelativeDimension_zero
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogCanon

theorem restr_top_surj {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (h : O = ⊤)
    (x : H0 p B O) : ∃ g : H0 p B ⊤, H0.restr le_top g = x := by
  subst h
  refine ⟨x, ?_⟩
  show (LB.toMod B).presheaf.map (homOfLE (le_refl (⊤ : Y.Opens))).op x = x
  rw [show (homOfLE (le_refl (⊤ : Y.Opens))).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem dimFlag_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (h : ¬ 1 ≤ Dw.p + Dw.q) : dimFlag Dw = 0 := by
  have : Dw.p + Dw.q = 0 := by omega
  simp [GlobalTheory.FlagTan.dimFlag, this]

theorem logCanon_iff : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z hF M ω b s hs m
  have hV : IsVariety₀ TF.X Z := GlobalTheory.T.flagSpace_component_smooth_projective_connected E H Dw l Xo c TF Z hF
  by_cases hpq : 1 ≤ Dw.p + Dw.q
  · have hKS : (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) := fun K _ _ y => GlobalTheory.T.kodaira_spencer_iso_flag_tangent hP hG E H Dw l Xo c K y hpq
    obtain ⟨ω₀⟩ := GlobalTheory.T.nonempty_kodairaSpencer_identification_offBoundary hP.p5 E H Dw l Xo c TF.Y TF.X Z (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) hKS
    exact (GlobalTheory.T.canonical_modification_ks_iso hP hG E H Dw l Xo c TF Z hF hKS hV ω₀ b s hs m).trans (GlobalTheory.T.canonical_modification_ks_iso_sec hP hG E H Dw l Xo c TF Z hF hKS hV ω₀ M ω b s hs m)
  · have h0 := dimFlag_eq_zero Dw hpq
    have hU : U₀ TF.X Z = ⊤ := GlobalTheory.T.dense_open_eq_univ_of_smooth_relDim_zero c.F _ (str₀ TF.X Z) (h0 ▸ hV.1) _ (dense_U₀ TF.X Z)
    have hall : ∀ y, y ∈ U₀ TF.X Z := fun y => hU.symm ▸ (Set.mem_univ y : y ∈ ((⊤ : (Y₀ TF.X Z).Opens) : Set _))
    have hoff : M.off = ⊤ := eq_top_iff.2 fun x _ => M.off_eq.ge (hall _)
    refine iff_of_true ?_ (restr_top_surj hoff _)
    obtain ⟨g, hg⟩ := restr_top_surj hU m
    refine ⟨g, fun y hy => (hy (hall y)).elim, hg⟩

end GlobalTheory.LogCanon
end
end
