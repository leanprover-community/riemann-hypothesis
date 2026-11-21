import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.UpConjLift

variable {D : D7}

theorem negSp_neg (S : HSp D) : negSp (GlobalTheory.Grid.neg S) = S := by
  cases S
  simp only [negSp, GlobalTheory.Grid.sgn, cond_true, neg_neg, Prod.swap_swap]

theorem isAutFunSm_of_eq {θ : InfFam D} {S₂ S : HSp D} (e : S₂ = S) {F : GA D S₂ → ℂ} {F' : GA D S → ℂ}
    (hF : ∀ x y, x ≍ y → F x = F' y) (h : IsAutFunSm θ S₂ F) : IsAutFunSm θ S F' := by
  subst e
  have : F = F' := funext fun x => hF x x HEq.rfl
  rwa [← this]

def j2 (S : HSp D) (y : GA D S) : GA D (negSp (GlobalTheory.Grid.neg S)) :=
  negGA (GlobalTheory.Grid.neg S) ((GlobalTheory.Grid.ofSgn true S).symm y)

theorem doubleNegSpaceUnitaryElement_heq (S : HSp D) (y : GA D S) : j2 S y ≍ y := by
  refine (Subtype.heq_iff_coe_eq fun z => ?_).2 rfl
  show z ∈ HR (AF D.host.F) D.sp.cm.sig (-(-S.gram)) ↔ z ∈ HR (AF D.host.F) D.sp.cm.sig S.gram
  rw [neg_neg]

theorem conj_lift (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ}
    {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} (ω : GlobalTheory.Grid.WRep S T)
    (hw : IsWeilDatumO ψ (GlobalTheory.Grid.neg S) T χS χT (ω.toSgn true)) {Φ : WO S T → ℂ}
    (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.neg S) T Φ) {μ : Measure (GA D T)} {𝓕 : Set (GA D T)} (hq : GlobalTheory.Mem.Th.IsQuot T μ 𝓕)
    {φ : GA D T → ℂ} (hφ : GlobalTheory.Mem.Th.IsCuspForm θ T φ) :
    (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO ω h g Φ) * φ g) 𝓕 μ) ∧
      IsAutFunSm θ S fun h => ∫ g in 𝓕, starRingEnd ℂ (thetaKO ω h g Φ) * φ g ∂μ := by
  have hw2 := GlobalTheory.ConjWeil.weil_conjSource D ψ (GlobalTheory.Grid.neg S) T χS χT (ω.toSgn true) hw
  have K := (GlobalTheory.Mem.Lift.isKerSys_thKer hθ hw2.std (GlobalTheory.Ker.isWeak_of_datum hw2) hw2.om_cont).swap
  have hf : IsThetaFunO ψ (negSp (GlobalTheory.Grid.neg S)) T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id Φ) :=
    ((GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std (GlobalTheory.Grid.neg S) T).1 Φ).2.2 hΦ
  obtain ⟨h1, h2⟩ := K.lift hP hθ hq hφ ⟨_, hf⟩
  have key : ∀ y g, GlobalTheory.Mem.Lift.swapKer (GlobalTheory.Mem.Lift.thKer ψ _ T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (ω.toSgn true)))
      ⟨_, hf⟩ g (j2 S y) = starRingEnd ℂ (thetaKO ω y g Φ) := by
    intro y g
    show starRingEnd ℂ (ω (y, g) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id Φ)) 0) = starRingEnd ℂ (ω (y, g) Φ 0)
    rw [GlobalTheory.ConjWeil.cj_id_cj_id]
  refine ⟨fun h => ?_, isAutFunSm_of_eq (negSp_neg S) (fun x y hxy => ?_) h2⟩
  · have := h1 (j2 S h)
    simp only [key] at this
    exact this
  · have e : x = j2 S y := eq_of_heq (hxy.trans (doubleNegSpaceUnitaryElement_heq S y).symm)
    subst e
    simp only [key]

end GlobalTheory.UpConjLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.UpConjLift

theorem up_isAutFunSm : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P i) φ → (∀ h, IntegrableOn (fun g => starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g) (G.mP i).fd (G.mP i).ν) → IsAutFunSm R.θ (G.P (i + 1)).V (fun h => ∫ g in (G.mP i).fd, starRingEnd ℂ (thetaKO (G.dn i).ω h g Φ) * φ g ∂(G.mP i).ν) := by
  intro _ hPr D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ _
  have hq : GlobalTheory.Mem.Th.IsQuot (G.P i).V (G.mP i).ν (G.mP i).fd := by
    have := (hG.meas.P i hi.le).2 (by omega)
    exact ⟨this.1.1, this.2⟩
  exact (conj_lift hPr.cuspRapidDecay hR.inf (G.dn i).ω (hG.arrows.dn i hi).weil hΦ hq ⟨hφ.1, hφ.2.1⟩).2

end GlobalTheory.UpConjLift
end
end
