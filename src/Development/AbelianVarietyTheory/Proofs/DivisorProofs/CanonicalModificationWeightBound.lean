import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleWeightGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullTopInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsFiniteSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionVanishes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltLocusFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalIntegralWeightSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv

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

namespace GlobalTheory.HSApp.BigMoving

theorem dim_eq : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    SmoothOfRelativeDimension D p → topologicalKrullDim X = D := by
  intro k _ X _ p D hp
  have hc (U : X.Opens) (hU : IsAffineOpen U) (h : (U : Set X).Nonempty) :
      topologicalKrullDim (U : Set X) = D := by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U))).trans
      (GlobalTheory.SmoothDim.ringKrullDim_affineOpen k X p D hp U hU h)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top x)
    exact ⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top (genericPoint X))
    exact (hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

end GlobalTheory.HSApp.BigMoving
end
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
namespace GlobalTheory.NadelSep
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh

theorem topologicalKrullDim_eq (S : LinSys ℂ) (h : S.IsVariety) : topologicalKrullDim S.Y = S.D := by
  have := h.isIntegral
  have hc (U : S.Y.Opens) (hU : IsAffineOpen U) (hne : (U : Set S.Y).Nonempty) :
      topologicalKrullDim (U : Set S.Y) = S.D := by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(S.Y, U))).trans
      (SmoothDim.ringKrullDim_affineOpen ℂ _ S.str _ h.smooth U hU hne)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    exact ⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top (genericPoint S.Y))
    exact (hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

end GlobalTheory.NadelSep
end
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
open GlobalTheory.Vanishing.H0
open GlobalTheory.Vanishing.H0

namespace GlobalTheory.CuspTransfer

theorem exists_cusp_germ : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed Xo c → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw), FlagTan.kap Dw + b = s → vanBd TF.X Z s ≤ space TF.X Z U s → ∃ F : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤ → Cusp Z U s, ∀ (z : M.X) (hz : z ∈ M.off) (j : (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).ι) (hj : z ∈ (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).U j) (i : (L₀ TF.X Z s).ι) (hi : M.σ z ∈ (L₀ TF.X Z s).U i), ∃ u : (M.X.presheaf.stalk z)ˣ, ∀ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, germ j z (memTop z) hj g = u.val * (M.σ.stalkMap z).hom (germ i (M.σ z) (M.off_eq.le hz) hi (cuspSec TF.X Z U s (F g))) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z r U hF M ω b s hs hvs
  set C := ((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs with hC
  have key : ∀ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, ∃ f : Cusp Z U s,
      C.mul ω.ω (M.pullOff (cuspSec TF.X Z U s f)) = H0.restr le_top g := by
    intro g
    obtain ⟨m, hm⟩ := (M.bijective_pullOff (isLB_L₀ TF.X Z s)).2 ((C.mulEquiv ω.unit).symm (H0.restr le_top g))
    have hm' : C.mul ω.ω (M.pullOff m) = H0.restr le_top g := by
      rw [hm, ← ProdChart.mulEquiv_apply C ω.unit, LinearEquiv.apply_symm_apply]
    obtain ⟨g', hv, hr⟩ := (GlobalTheory.T.canonical_ideal_weight_section hP hG E H Dw l Xo c TF Z hF M ω b s hs m).2 ⟨g, hm'.symm⟩
    refine ⟨ofSpace TF.X Z U s ⟨g', hvs hv⟩, ?_⟩
    rw [cuspSec_ofSpace]
    exact (congrArg (fun x => C.mul ω.ω (M.pullOff x)) hr).trans hm'
  refine ⟨fun g => (key g).choose, ?_⟩
  intro z hz j hj i hi
  obtain ⟨t, ha, hb, hc⟩ := C.cover z
  have hω : IsUnit (H0.germ (C.a t) z hz ha ω.ω) := ω.unit z hz (C.a t) ha
  refine ⟨tr _ z j (C.c t) * hω.unit *
      Units.map (M.σ.stalkMap z).hom.toMonoidHom (tr (L₀ TF.X Z s) (M.σ z) (C.b t PUnit.unit) i), ?_⟩
  intro g
  have hg := (key g).choose_spec
  rw [H0.germ_change j (C.c t) z (memTop z) hj hc g, ← H0.germ_restr le_top (C.c t) z hz hc g, ← hg,
    C.germ_mul ω.ω _ t z hz ha hb hc]
  change _ = _ * (M.σ.stalkMap z).hom _
  have e2 := H0.germ_pull M.σ M.off_eq.le (C.b t) z hz hb (cuspSec TF.X Z U s (key g).choose)
  change _ * (_ * H0.germ (C.b t) z hz hb (H0.pull M.σ M.off_eq.le (cuspSec TF.X Z U s (key g).choose))) = _
  rw [e2]
  erw [H0.germ_change (B := L₀ TF.X Z s) (C.b t PUnit.unit) i (M.σ z) (M.off_eq.le hz) _ hi, map_mul]
  simp only [Units.val_mul, IsUnit.unit_spec, Units.coe_map]
  simp only [mul_assoc]
  rfl

end GlobalTheory.CuspTransfer
end
