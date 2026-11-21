import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqOfExhaustive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2OfDecompositionStatement

section
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Per.AmbFil

theorem filCount_at (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {n : ℕ}
    (M : Br.G D.nbr i w hw →* Matrix (Fin n) (Fin n) ↥C.LL.1) :
    EmbeddingTypes.FilCount (Br.PD D.loc D.nbr i w hw) (matRep M) := by
  intro τ J hJ
  exact GlobalTheory.Per.FilCount.fil_count (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL _ (matRep M) τ J hJ

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), EmbeddingTypes.ambFil (D := D) i r ρ π dc := by
  intro D i r ρ π dc
  exact ⟨fun w hw _ C x => filCount_at D i w hw C _,
    fun _ => ⟨fun w hw _ C => filCount_at D i w hw C _, fun w hw _ C => filCount_at D i w hw C _⟩⟩

end GlobalTheory.Per.AmbFil
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientFiltration_every_declaration : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), EmbeddingTypes.ambFil (D := D) i r ρ π dc := by
  atlas_forward_decl GlobalTheory.Per.AmbFil.main
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.MainNotions.TruncatedSeriesCountingIdentities (Decl CoefExt locC chi1C)

namespace GlobalTheory.AmbWT

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : CoefExt D i w hw)

def coef : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL

def grp (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Br.G D.nbr i w hw →* GE D.nd :=
  (decS D.nd w).comp (Br.iota D.nbr i w hw)

theorem locC_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    locC C M g = (M (grp hw g)).map (coef C) := rfl

theorem localizedCoefficientChar_apply (g : Br.G D.nbr i w hw) :
    chi1C C g = Units.map (coef C : D.nd.O i →* ↥C.LL.1) (chiU D.nd i 1 (grp hw g)) := rfl

theorem locC_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    locC C (rTwO D.nd i r x) = twistM (locC C (rO D.nd i r x)) (chi1C C)⁻¹ := by
  refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
  rw [locC_apply]
  show coef C ((((chiU D.nd i 1)⁻¹ (grp hw g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (grp hw g) a b) =
    ((((chi1C C)⁻¹ g) : (↥C.LL.1)ˣ) : ↥C.LL.1) * (locC C (rO D.nd i r x) g) a b
  rw [map_mul, locC_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, localizedCoefficientChar_apply]
  rfl

open Classical in

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambW (D := D) i ρ π dc ∧ EmbeddingTypes.ambT2 (D := D) i ρ π dc := by
  intro D i r ρ π dc hG hd
  have hd' : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
    obtain ⟨e, he⟩ := hd
    refine ⟨e, fun g u => ?_⟩
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.overK, GlobalTheory.SummandJumps.matRep_apply]
    exact he g u
  have hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : CoefExt D i w hw),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (WpO D.nd i ρ π))) ∧
        IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (T2O D.nd i ρ π))) := by
    intro w hw C
    have h1 := (hG w hw C).2 π
    rw [← locC_rTwO] at h1
    exact (GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd').1 h1
  refine ⟨fun _ w hw _ C => (hc w hw C).1, fun _ w hw _ C => ⟨(hc w hw C).2, ?_, ?_⟩⟩
  · exact (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) (D.nbr i w hw).Kw C.LL _ _ (hc w hw C).2).1
  · exact (hG w hw C).1.2.2.2.2.2.2

end GlobalTheory.AmbWT
end
end

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientDual_crystalline_and_pure_of_decomp : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambW (D := D) i ρ π dc ∧ EmbeddingTypes.ambT2 (D := D) i ρ π dc := by
  atlas_forward_decl GlobalTheory.AmbWT.main
end

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HubGood

theorem ambAll_goodPoints : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (X : KillingConditions.HubData D), AdmissibleParameterJ.DeRhamFamilyAway D → AdmissibleParameterJ.ConclusionJa D → AdmissibleParameterJ.jcCondition L → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambT2 (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambW (D := D) i (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambFil (D := D) i (X.r i) (X.ρ i) π (X.dc i) ∧ EmbeddingTypes.ambBlock (D := D) i (X.r i) (X.ρ i) π := by
  intro hF D L X hG hJa hJc hX i hl π hπ
  have hZ := LargeLevelLemmas.zgoodSubsetZ i hπ
  have hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i (X.r i) (X.ρ i) π := by
    obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
    exact ⟨e, fun g u => he g u⟩
  have h0 : D.nd.l i ≠ D.host.g 0 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have h1 : D.nd.l i ≠ D.host.g 1 := fun h => hl (by simp [TwistedPlaces.gset, h])
  have hg2 := GlobalTheory.T.admG2_of_decomposition hF D L hG hJa hJc i (X.r i) (X.ρ i) π (hX.good i) h0 h1 hZ hd
  have hWT := GlobalTheory.T.ambientDual_crystalline_and_pure_of_decomp D i (X.r i) (X.ρ i) π (X.dc i) hg2 hd
  exact ⟨hWT.2, hWT.1, GlobalTheory.T.ambientFiltration_every_declaration D i (X.r i) (X.ρ i) π (X.dc i), GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition D i (X.r i) (X.ρ i) π hd⟩

end GlobalTheory.HubGood
end
