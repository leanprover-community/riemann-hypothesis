import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalLevelData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyLocalConditionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyLocalCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigensystemMultiplicitiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigensystemMultiplicities
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyTraceFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyTraceFrobenius
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompactOpenMembershipStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompactOpenMembership
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMuUnrFrobStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPolarized
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SGoodOfLevelShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompAtEqOneOfTameAt
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyDeterminant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyCrystallineWeightsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyCrystallineWeights

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.HeckePointUniq
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem eq_of_eigen_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (V : Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i))), V ≠ ⊥ → ∀ x x' : X.nd.X i, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) → (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x') • (mlX M X i).real y) → x = x' := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i V hV x x' hx hx'
  classical
  obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  have hry : (mlX M X i).real y ≠ 0 := fun h =>
    hy0 ((mlX M X i).real_inj (by rw [h, map_zero]))
  have hιinj : Function.Injective (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp
      (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) :=
    ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).injective.comp (Sp.iq i).injective).comp
      (IsFractionRing.injective (X.nd.O i) (FractionRing (X.nd.O i)))
  have key : ∀ v k, SplitOut X.nd i v → 1 ≤ k → k ≤ D.R.nV →
      (X.nd.hT i v k : X.nd.X i → X.nd.O i) x = (X.nd.hT i v k : X.nd.X i → X.nd.O i) x' := by
    intro v k hv hk1 hk2
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hv.1
    have e1 := hx v k s ϖ hv hc hu hk1 hk2 y hyV
    have e2 := hx' v k s ϖ hv hc hu hk1 hk2 y hyV
    rw [e1] at e2
    exact hιinj (smul_left_injective ℂ hry e2)
  have hTle : X.nd.T i ≤ AlgHom.equalizer (Pi.evalAlgHom (X.nd.O i) (fun _ : X.nd.X i => X.nd.O i) x)
      (Pi.evalAlgHom (X.nd.O i) (fun _ : X.nd.X i => X.nd.O i) x') := by
    rw [← X.nd.T_gen i]
    refine Algebra.adjoin_le ?_
    rintro f ⟨v, k, h1, h2, h3, h4, hk1, hk2, rfl⟩
    exact key v k ⟨h1, h2, h3, h4⟩ hk1 hk2
  by_contra hne
  obtain ⟨f, hf, hfx⟩ := X.nd.T_sep i x x' hne
  exact hfx (hTle hf)
end GlobalTheory.HeckePointUniq
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_local_condition_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (V : Submodule ℂ (D.what₂.Mt (X.nd.mu i) (X.nd.j i))), V ≠ ⊥ → ∀ x x' : X.nd.X i, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) → (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ V, NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x') • (mlX M X i).real y) → x = x' := by
  atlas_forward_decl _root_.GlobalTheory.HeckePointUniq.eq_of_eigen_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutPts
end GlobalTheory.AutPts
namespace GlobalTheory.AutPts
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem automorphic_points_exist : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → (∀ x, ∃ P, ptV P = some x) ∧ ∀ x, X.nd.mult i x = Module.finrank ℂ ↥(⨆ P ∈ {P | ptV P = some x}, ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i ι _ F irr hinj hsurj hne hind
    htop ptV hpt
  classical
  have hmem : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hj1 : X.nd.j i - 1 + 1 = X.nd.j i := by have := X.nd.j_range i; omega
  let jf : Fin D.R.m := ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩
  let B := gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)
  have hprod : NG.IsProdLevel (mlX M X i).J :=
    mt_tr M (fun _ _ Mr => NG.IsProdLevel Mr.J) (X.nd.mu_w i).symm hj1 _ _ _ _ (hMI.prod (X.nd.w i) jf)
  have hhyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ B :=
    mt_tr M (fun _ _ Mr => NG.HypOutside Mr.J Mr.χ B) (X.nd.mu_w i).symm hj1 _ _ _ _ (hMI.hyp (X.nd.w i) jf)
  have hbad : ∀ w (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → s.v ∉ B :=
    fun w s hw hc => l0 D cf C tp A.pl M big X T Sp i w s hw hc
  have hlin : ∀ w k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → ∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (mlX M X i).wt.W),
      NG.tN (mlX M X i).J s ϖ k (c • f + f') = c • NG.tN (mlX M X i).J s ϖ k f + NG.tN (mlX M X i).J s ϖ k f' := by
    intro w k s ϖ hw hc hu c f f'
    have hfin := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (mlX M X i).J (mlX M X i).χ B hhyp s ϖ k (hbad w s hw hc) hu
    simp only [NG.tN]
    rw [GlobalTheory.PtLocalEig.heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]
  let Par := PlE D.host × ℕ × (Σ s : SplitPlace D.host.E, s.v.adicCompletion (maximalRealSubfield D.host.E))
  let Good : Par → Prop := fun p => SplitOut X.nd i p.1 ∧ IsConjPl D.host p.1 p.2.2.1.w ∧
    IsUnif D.host.E p.2.2.1.v p.2.2.2 ∧ 1 ≤ p.2.1 ∧ p.2.1 ≤ D.R.nV
  let op : Par → (GAf D.host.E D.R.nV → (mlX M X i).wt.W) → (GAf D.host.E D.R.nV → (mlX M X i).wt.W) :=
    fun p => NG.tN (mlX M X i).J p.2.2.1 p.2.2.2 p.2.1
  let io : X.nd.O i →+* ℂ := ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp
    (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))
  let lam : X.nd.X i → Par → ℂ := fun x p => io ((X.nd.hT i p.1 p.2.1 : X.nd.X i → X.nd.O i) x)
  have hdec : ∀ x y, y ∈ (⨆ P ∈ {P | ptV P = some x}, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real) ↔
      ∀ p, Good p → op p ((mlX M X i).real y) = lam x p • (mlX M X i).real y := by
    intro x y
    refine mem_iSup_iff (mlX M X i).real (mlX M X i).real_inj _ hind htop Good op
      (fun p hp => hlin _ _ _ _ hp.1 hp.2.1 hp.2.2.1) (fun P p hp => ?_) (lam x) (fun P => ptV P = some x)
      (fun P => ?_) y
    · exact l1 D (X.nd.mu i) (X.nd.j i) (mlX M X i) B hprod hhyp (F P) (irr P) p.2.2.1 p.2.2.2 p.2.1
        (hbad _ _ hp.1 hp.2.1) hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
    · rw [hpt P x]
      constructor
      · rintro h ⟨w, k, s, ϖ⟩ ⟨hw, hc, hu, hk1, hk2⟩ z hz
        exact h w k s ϖ hw hc hu hk1 hk2 z hz
      · intro h w k s ϖ hw hc hu hk1 hk2 z hz
        exact h ⟨w, k, s, ϖ⟩ ⟨hw, hc, hu, hk1, hk2⟩ z hz
  have hinjC : Function.Injective (Sp.iotaC (X.nd.j i) (X.nd.w i)) := by
    intro a b hab
    obtain ⟨a', rfl⟩ := (Sp.phO _ _ i hmem).surjective a
    obtain ⟨b', rfl⟩ := (Sp.phO _ _ i hmem).surjective b
    rw [← Sp.iotaC_coh, ← Sp.iotaC_coh] at hab
    have hio : Function.Injective io :=
      (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).injective.comp ((Sp.iq i).injective.comp
        (IsFractionRing.injective (X.nd.O i) (FractionRing (X.nd.O i))))
    rw [hio hab]
  let φ : FractionRing (Sp.B.Oc (X.nd.j i) (X.nd.w i)) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = Sp.iotaC _ _ z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (Sp.phK _ _ i hmem).toRingHom =
      (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (X.nd.O i))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Sp.phK_alg, hφalg]
    rw [← Sp.iotaC_coh]
  have hφ : ∀ y, φ (Sp.B.ec _ _ y) = D.what₂.embLL y := by
    intro y
    rw [← Sp.phK_emb _ _ i hmem y, ← Sp.iq_LL i y]
    exact congrArg (fun f : FractionRing (X.nd.O i) →+* ℂ => f (X.nd.embK i y)) hφK
  have hdim : ∀ x, X.nd.mult i x = Module.finrank ℂ
      ↥(⨆ P ∈ {P | ptV P = some x}, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real) := by
    intro x
    rw [l2a D A.pl M C big X T Sp (X.nd.j i) (X.nd.w i) i hmem x]
    refine l2b D M Sp.B (X.nd.j i) (X.nd.w i) (X.nd.mu i) (X.nd.j_range i).1 (X.nd.j_range i).2 (X.nd.mu_w i) φ hφ
      (fun v k => algebraMap _ _ (Sp.phO _ _ i hmem ((X.nd.hT i v k : X.nd.X i → X.nd.O i) x))) _ ?_ ?_ ?_
    · intro v k hvk
      exact GlobalTheory.T.splitEx_every_datum D v hvk.1
    · intro v k s ϖ hvk hc hu c f f'
      exact hlin v k s ϖ ((genAt_iff' Sp i v k).1 hvk).1 hc hu c f f'
    · intro y
      rw [hdec x y]
      constructor
      · intro h v k s ϖ hvk hc hu
        obtain ⟨hv, hk1, hk2⟩ := (genAt_iff' Sp i v k).1 hvk
        have e := h ⟨v, k, s, ϖ⟩ ⟨hv, hc, hu, hk1, hk2⟩
        rw [hφalg, ← Sp.iotaC_coh]
        exact e
      · rintro h ⟨v, k, s, ϖ⟩ ⟨hv, hc, hu, hk1, hk2⟩
        have e := h v k s ϖ ((genAt_iff' Sp i v k).2 ⟨hv, hk1, hk2⟩) hc hu
        rw [hφalg, ← Sp.iotaC_coh] at e
        exact e
  refine ⟨fun x => ?_, hdim⟩
  by_contra hno
  push_neg at hno
  have hbot : (⨆ P ∈ {P | ptV P = some x}, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real) = ⊥ :=
    eq_bot_iff.2 (iSup₂_le fun P hP => absurd hP (hno P))
  have h0 := hdim x
  rw [hbot, finrank_bot] at h0
  have hne0 := X.nd.eig_ne i x
  apply hne0
  have : Module.Finite (FractionRing (X.nd.O i)) (TensorProduct (X.nd.O i) (FractionRing (X.nd.O i)) (X.nd.Mt i)) :=
    inferInstance
  exact Submodule.finrank_eq_zero.1 h0
end GlobalTheory.AutPts
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_unramified_outside_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → (∀ x, ∃ P, ptV P = some x) ∧ ∀ x, X.nd.mult i x = Module.finrank ℂ ↥(⨆ P ∈ {P | ptV P = some x}, ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) := by
  atlas_forward_decl _root_.GlobalTheory.AutPts.automorphic_points_exist
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutUnr
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem locV_unr_m_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), IsSplitPl D.host w → w ∉ X.nd.Q i → (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) → D.naut.unr (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop P w hw hQ hg hp
  classical
  obtain ⟨s, hsw⟩ := exists_splitPlace_eq D w hw
  have hov : NG.OverPl w s.v := hsw ▸ s.w_under
  have hjf : X.nd.j i - 1 + 1 = X.nd.j i := by have := X.nd.j_range i; omega
  let jf : Fin D.R.m := ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩
  have h0 := hMI.hyp (X.nd.w i) jf
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)) :=
    GlobalTheory.FitHecke.hypOutside_transport' (M := M) (X.nd.mu_w i).symm hjf _ _ (X.nd.j_range i).1 (X.nd.j_range i).2 _ h0
  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQe : C.Q (X.nd.w i) = Sp.B.Qc (X.nd.j i) (X.nd.w i) := (Sp.Qc_eq _ _).symm
  have hvB : s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf) := by
    rintro (⟨w', hov', k, hk⟩ | hq)
    · exact hg k (mem_placesOver_of_overPl hov hov' hk)
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i) jf hq
      rcases hw' with hQ' | hp'
      · rw [hQe] at hQ'
        have hwQ : w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) := Sp.B.Qc_over _ _ w' w hQ' ⟨s.v, hov', hov⟩
        rw [← Sp.Q_eq _ _ i hi] at hwQ
        exact hQ hwQ
      · rw [X.nd.w_l i] at hp'
        exact hp (mem_placesOver_of_overPl hov hov' hp')
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne P)
  have hfix : ∀ κ ∈ {κ : GAf D.host.E D.R.nV | κ ∈ Umax D.host.E D.R.nV ∧ TrivOutside {s.v} κ},
      NG.rt D.host.E D.R.nV κ ((mlX M X i).real y) = (mlX M X i).real y := by
    rintro κ ⟨hU, htr⟩
    have htr' : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf))ᶜ κ := by
      intro v hv
      apply htr v
      rintro rfl
      exact hv hvB
    obtain ⟨hJ, hχ⟩ := hyp κ htr'
    have hκ : κ ∈ (mlX M X i).J := hJ.2 hU
    have hmem : (mlX M X i).real y ∈ NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ := by
      rw [← (mlX M X i).real_range]; exact ⟨y, rfl⟩
    have e := hmem.2 ⟨κ, hκ⟩
    rw [hχ hκ] at e
    simpa using e
  have hr0 : (mlX M X i).real y ≠ 0 := fun h =>
    hy0 ((mlX M X i).real_inj (h.trans (map_zero _).symm))
  obtain ⟨f, hf, hf0, hff⟩ := exists_fixed_of_isoTyp (mlX M X i).wt.ρ (irr P).1.stable _ hy hr0 hfix
  have hsph : _root_.UpperTheory.One.M.SphAtG { (mlX M X i).wt with S := F P, irrS := irr P } s.v :=
    _root_.UpperTheory.One.M.New.sphMk ⟨f, hf, hf0, fun κ hU htr => hff κ ⟨hU, htr⟩⟩
      fun h => absurd rfl (h s)
  rw [← hsw]
  exact A.au.locUnr _ _ _ _ s hsph
end GlobalTheory.AutUnr
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_irreducible_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), IsSplitPl D.host w → w ∉ X.nd.Q i → (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) → D.naut.unr (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) := by
  atlas_forward_decl _root_.GlobalTheory.AutUnr.locV_unr_m_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.LocLevel
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem level_at_splitOut_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hMI : MtInput D M tp.tup C.Q) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → ∀ κ : GAf D.host.E D.R.nV, TrivOutside {s.v} κ → (κ ∈ (mlX M X i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ h : κ ∈ (mlX M X i).J, (mlX M X i).χ ⟨κ, h⟩ = 1 := by
  intro D cf jE A M C tp hMI big X T Sp i w s hw hc κ htr
  classical
  have hov : NG.OverPl w s.v := overPl_of_isConjPl hc
  have hjf : X.nd.j i - 1 + 1 = X.nd.j i := by have := X.nd.j_range i; omega
  let jf : Fin D.R.m := ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩
  have h0 := hMI.hyp (X.nd.w i) jf
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)) :=
    GlobalTheory.FitHecke.hypOutside_transport' (M := M) (X.nd.mu_w i).symm hjf _ _ (X.nd.j_range i).1 (X.nd.j_range i).2 _ h0
  have hS := (X.nd.S_def i w).not.1 hw.2.2.1
  have hl := hw.2.1
  have hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hk
    apply hS
    refine ⟨?_, hl⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hp : w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) :=
    fun h => hS ⟨Or.inr (Or.inr h), hl⟩
  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQe : C.Q (X.nd.w i) = Sp.B.Qc (X.nd.j i) (X.nd.w i) := (Sp.Qc_eq _ _).symm
  have hvB : s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf) := by
    rintro (⟨w', hov', k, hk⟩ | hq)
    · exact hg k (mem_placesOver_of_overPl' hov hov' hk)
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i) jf hq
      rcases hw' with hQ' | hp'
      · rw [hQe] at hQ'
        have hwQ : w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) := Sp.B.Qc_over _ _ w' w hQ' ⟨s.v, hov', hov⟩
        rw [← Sp.Q_eq _ _ i hi] at hwQ
        exact hw.2.2.2 hwQ
      · rw [X.nd.w_l i] at hp'
        exact hp (mem_placesOver_of_overPl' hov hov' hp')
  have htr' : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf))ᶜ κ := by
    intro v hv
    apply htr v
    rintro rfl
    exact hv hvB
  exact hyp κ htr'
end GlobalTheory.LocLevel
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_j_iff_umax_and_chi_eq_one_of_split_out : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hMI : MtInput D M tp.tup C.Q) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → ∀ κ : GAf D.host.E D.R.nV, TrivOutside {s.v} κ → (κ ∈ (mlX M X i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ h : κ ∈ (mlX M X i).J, (mlX M X i).χ ⟨κ, h⟩ = 1 := by
  atlas_forward_decl _root_.GlobalTheory.LocLevel.level_at_splitOut_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.AutPart
theorem heckePol_map_eq_frobPol_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → ∀ P x, ptV P = some x → ∀ w, SplitOut X.nd i w → (heckePol X.nd i x w).map (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) = ((D.naut.frobEig (D.naut.lpTw (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) ((1 - (D.R.nV : ℝ)) / 2))).map fun α => Polynomial.X - Polynomial.C α).prod := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop ptV hpt P x hx w hw
  obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw.1
  have heig := (hpt P x).1 hx
  have hlev := _root_.GlobalTheory.T.mem_j_iff_umax_and_chi_eq_one_of_split_out D cf jE A M C tp hMI big X T Sp i w s hw hc
  have hne' : Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P) ⊓ Formalism.L2.NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne P)
    rw [Submodule.ne_bot_iff]
    refine ⟨(mlX M X i).real y, ⟨hy, ?_⟩, fun h0 => hy0 ((mlX M X i).real_inj (h0.trans (map_zero _).symm))⟩
    rw [← (mlX M X i).real_range]; exact LinearMap.mem_range_self _ _
  obtain ⟨f, ⟨hfF, hfT⟩, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (GlobalTheory.T.inf_typeSpace_ne_bot_of_isotypicPart (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ (F P) (irr P).1 hne')
  have hfR : f ∈ LinearMap.range (mlX M X i).real := by rw [(mlX M X i).real_range]; exact hfT
  obtain ⟨y, rfl⟩ := hfR
  have hyV : y ∈ (Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real := by
    show (mlX M X i).real y ∈ Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P)
    exact (le_sSup (show F P ∈ {S' | Formalism.L2.NG.IsIrrRep (mlX M X i).wt.ρ S' ∧ Formalism.L2.NG.IsoRep (F P) S'} from
      ⟨irr P, LinearEquiv.refl ℂ _, fun h f f' e => e⟩)) hfF
  have hsph : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      Formalism.L2.NG.rt D.host.E D.R.nV κ ((mlX M X i).real y) = (mlX M X i).real y := by
    intro κ hκ ht
    have hJ : κ ∈ (mlX M X i).J := ((hlev κ ht).1).2 hκ
    have := hfT.2 ⟨κ, hJ⟩
    rw [this, (hlev κ ht).2 hJ]; simp
  have hpol := A.au.locPol (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
    { (mlX M X i).wt with S := F P, irrS := irr P } s w ϖ hc hu (mlX M X i).J (fun κ ht => (hlev κ ht).1)
    ((mlX M X i).real y) hfF hf0 hsph
    (fun k => (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x))
    (fun k hk1 hk2 => heig w k s ϖ hw hc hu hk1 hk2 y hyV)
  refine Eq.trans ?_ hpol
  simp [heckePol, Polynomial.map_sum]
end GlobalTheory.AutPart
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_trace_frobenius_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → ∀ P x, ptV P = some x → ∀ w, SplitOut X.nd i w → (heckePol X.nd i x w).map (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) = ((D.naut.frobEig (D.naut.lpTw (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) ((1 - (D.R.nV : ℝ)) / 2))).map fun α => Polynomial.X - Polynomial.C α).prod := by
  atlas_forward_decl _root_.GlobalTheory.AutPart.heckePol_map_eq_frobPol_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.SphNonSplit
set_option maxHeartbeats 2000000 in
theorem sphAU_of_not_split_m_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), ¬ IsSplitPl D.host w → D.nbc.sphAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _hCS hMI _hstar _hE hsp _hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop P w hns
  set v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w with hv
  have hover : NG.OverPl w v := rfl
  rw [A.au.sph (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 _ w v hns hover]
  obtain ⟨h1, h2⟩ := X.nd.j_range i
  let j : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = X.nd.j i := by simp only [j]; omega
  have hvB := not_mem_bad D cf C tp hsp (X.nd.w i) j w v hover hns
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
    have key : ∀ (μ : D.what₂.Tup) (jj : ℕ) (k1 : 1 ≤ jj) (k2 : jj ≤ D.R.m), μ = D.what₂.muTw (X.nd.w i) → jj = j.1 + 1 →
        NG.HypOutside (M μ jj k1 k2).J (M μ jj k1 k2).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j)) := by
      rintro μ jj k1 k2 rfl rfl
      exact hMI.hyp (X.nd.w i) j
    exact key _ _ _ _ (X.nd.mu_w i) hj.symm
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 (hne P)
  have hry : (mlX M X i).real y ≠ 0 := fun h0 =>
    hy0 ((mlX M X i).real_inj (h0.trans (map_zero (mlX M X i).real).symm))
  have hT : (mlX M X i).real y ∈ NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ := by
    rw [← (mlX M X i).real_range]; exact LinearMap.mem_range_self _ _
  obtain ⟨f, hfS, hf0, hfix⟩ := GlobalTheory.T.fixed_vector_of_mem_isotypic_component (mlX M X i).wt.ρ (F P)
    {κ | κ ∈ Umax D.host.E D.R.nV ∧ TrivOutside {v} κ} (irr P) _ hy hry (by
      rintro κ ⟨hU, htr⟩
      have ht : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j))ᶜ κ := fun u hu =>
        htr u (by rintro rfl; exact hu hvB)
      have hJ : κ ∈ (mlX M X i).J := ((hyp κ ht).1).2 hU
      rw [hT.2 ⟨κ, hJ⟩, (hyp κ ht).2 hJ, Units.val_one, one_smul])
  have hsh : ∀ (μ : D.what₂.Tup) (jj : ℕ) (k1 : 1 ≤ jj) (k2 : jj ≤ D.R.m), μ = D.what₂.muTw (X.nd.w i) → jj = j.1 + 1 →
      ∀ s : SplitPlace D.host.E, s.v ∈ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) j) → ∃ s₀ : SplitPlace D.host.E, s₀.v = s.v ∧
      ((∃ (r : ℕ) (ξ : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.LevelPara (M μ jj k1 k2).J (M μ jj k1 k2).χ s₀ r ξ) ∨
      ((∃ (g : ℕ) (_ : Fact g.Prime) (e : ℚ_[g] ≃+* s.w.adicCompletion D.host.E), Continuous e) ∧
        ∃ (r : ℕ) (ψ₀ : AddChar (s₀.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
          (ξ : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.LevelUni (M μ jj k1 k2).J (M μ jj k1 k2).χ s₀ r ψ₀ ξ ∧ NG.IsPsi0 s₀ ψ₀ ∧
          ∀ u : (s₀.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
            Valued.v ((u : s₀.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 → ξ u = 1)) := by
    rintro μ jj k1 k2 rfl rfl s hs
    by_cases hg : s.v ∈ gPl D
    · obtain ⟨k, v', s₀, hw, hv'⟩ := GlobalTheory.PlaceUnderFixed.exists_splitPlace_under_plGw D s hg
      obtain ⟨ψ₀, ξ, hψ, hc, hU⟩ := hMI.uni (X.nd.w i) j k v' s₀ hw
      refine ⟨s₀, hv', Or.inr ⟨GlobalTheory.SplitTypeCompl.exists_padic_equiv D s hg, D.R.r, ψ₀, ξ, hU, hψ,
        GlobalTheory.AVGood.compAt_eq_one_of_tameAt s₀ _ (fun x hx hx' => ?_) ξ hc⟩⟩
      rw [TupTied.tup, HChar.loc_mul, (cf.isMu0 j).tame _ x hx hx', tp.xi_tame _ _ x hx hx', one_mul]
    · obtain ⟨s₀, ξ, hv', -, hP⟩ := hMI.para (X.nd.w i) j s.v (hs.resolve_left hg)
      exact ⟨s₀, hv', Or.inl ⟨D.R.r, ξ, hP⟩⟩
  have hlev : GlobalTheory.RecT.Thread.LevelShape ({ (mlX M X i).wt with S := F P, irrS := irr P } : NG.AutRep D.host.E D.R.nV) :=
    ⟨(mlX M X i).J, (mlX M X i).χ, _, (mlX M X i).J_open, hyp, ⟨_, hy, hT, hry⟩, hsh _ _ _ _ (X.nd.mu_w i) hj.symm⟩
  have h0 : _root_.UpperTheory.One.M.New.Sph0 ({ (mlX M X i).wt with S := F P, irrS := irr P } : NG.AutRep D.host.E D.R.nV) v :=
    ⟨f, hfS, hf0, fun κ hU htr => hfix κ ⟨hU, htr⟩⟩
  exact _root_.UpperTheory.One.M.New.sphMk h0 fun _ =>
    GlobalTheory.RecT.Thread.good_of_levelShape UpperTheory.Zero.LLC.Pr.bz UpperTheory.Zero.LLC.Pr.zel _ hlev
end GlobalTheory.SphNonSplit
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.ResidueLocPlace
end GlobalTheory.ResidueLocPlace
namespace GlobalTheory.ResidueLocPlace
end GlobalTheory.ResidueLocPlace
theorem GlobalTheory.ResidueLocPlace.exists_residueField_map_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ κ : IsLocalRing.ResidueField (X.nd.O i) →+* Formalism.CyclotomicNorms.Fbar (X.nd.l i), ∀ y : X.nd.O i, ∃ h : (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) y ∈ A.pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (A.pl.plκ (X.nd.w i) (IsLocalRing.residue (A.pl.plB (X.nd.w i)) ⟨_, h⟩)) = κ (IsLocalRing.residue (X.nd.O i) y) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i
  exact GlobalTheory.ResidueLocPlace.exists_residue_lift (X.nd.w_l i) _ _ (A.pl.ι (X.nd.w i)) (A.pl.plB (X.nd.w i))
    (A.pl.plB_eq (X.nd.w i)) (A.pl.plκ (X.nd.w i)) (Sp.iq i) (Sp.iq_alg i)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_determinant_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ κ : IsLocalRing.ResidueField (X.nd.O i) →+* Formalism.CyclotomicNorms.Fbar (X.nd.l i), ∀ y : X.nd.O i, ∃ h : (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) y ∈ A.pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (A.pl.plκ (X.nd.w i) (IsLocalRing.residue (A.pl.plB (X.nd.w i)) ⟨_, h⟩)) = κ (IsLocalRing.residue (X.nd.O i) y) := by
  atlas_forward_decl _root_.GlobalTheory.ResidueLocPlace.exists_residueField_map_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.MuCLoc
theorem exists_muC_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ μ : D.naut.CG 1, D.naut.csd μ ∧ ∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i
  obtain ⟨h1, h2⟩ := X.nd.j_range i
  let j : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  refine ⟨A.chr.e1.symm ⟨tp.tup (X.nd.mu i) j, tp.tup_unitary (X.nd.mu i) j⟩, ?_, ?_⟩
  · rw [A.chr.csd, Equiv.apply_symm_apply]
    exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ ((cf.isMu0 j).triv.mul (tp.xi_triv (X.nd.mu i)))
  · intro j' hj'
    have : j' = j := Fin.ext (by simp only [j]; omega)
    subst this
    rw [Equiv.apply_symm_apply]
end GlobalTheory.MuCLoc
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_crystalline_weights_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ μ : D.naut.CG 1, D.naut.csd μ ∧ ∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j := by
  atlas_forward_decl _root_.GlobalTheory.MuCLoc.exists_muC_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.AutPart.exists_autSpec_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∃ (Y : LocAut X) (Cb : LocBC Y), Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb) := by
  intro hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp
  classical
  choose ι hfin F hF using fun i : X.nd.Loc => GlobalTheory.T.algebraicModularForms_irreducible_decomposition D (X.nd.mu i) (X.nd.j i) (mlX M X i)
  have irr : ∀ i P, NG.IsIrrRep (mlX M X i).wt.ρ (F i P) := fun i => (hF i).1
  have hinj := fun i => (hF i).2.1
  have hsurj := fun i => (hF i).2.2.1
  have hne := fun i => (hF i).2.2.2.1
  have hind := fun i => (hF i).2.2.2.2.1
  have htop := fun i => (hF i).2.2.2.2.2
  obtain ⟨ptV, hptV⟩ : ∃ ptV : ∀ i, ι i → Option (X.nd.X i), ∀ i P x, ptV i P = some x ↔
      (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) := by
    refine ⟨fun i P => if h : ∃ x, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) then some h.choose else none, fun i P x => ?_⟩
    dsimp only
    by_cases h : ∃ x, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)
    · rw [dif_pos h]
      constructor
      · rintro ⟨⟩; exact h.choose_spec
      · intro hx
        rw [_root_.GlobalTheory.T.galois_family_local_condition_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i _ (hne i P) _ _ h.choose_spec hx]
    · rw [dif_neg h]
      exact ⟨fun h' => absurd h' (by simp), fun hx => (h ⟨x, hx⟩).elim⟩
  have hpts := fun i => haveI := hfin i; _root_.GlobalTheory.T.galois_family_unramified_outside_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) (ptV i) (hptV i)
  choose μ hμc hμ using _root_.GlobalTheory.T.galois_family_crystalline_weights_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp
  choose κ hκ using _root_.GlobalTheory.T.galois_family_determinant_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp
  choose b hb using fun i : X.nd.Loc => GlobalTheory.algWt_contragredient D.host.E D.R.nV (mlX M X i).wt
  have hralg : ∀ {a} (π : D.naut.CG a) τ, D.naut.ralg π → ∀ z ∈ D.naut.infG π τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 :=
    fun π τ h => ((D.naut.ralg_def π).1 h τ).2
  refine ⟨{
    iotaQ := Sp.iq
    iotaQC := fun i => (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i)))
    iota_LL := Sp.iq_LL
    iotaQ_alg := Sp.iq_alg
    muC := μ
    muC_csd := hμc
    AV := ι
    finAV := hfin
    ptV := ptV
    typeV := fun i P => ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real)
    typeV_ne := hne
    typeV_indep := hind
    typeV_top := htop
    pt_surj := fun i => (hpts i).1
    eig_dim := fun i => (hpts i).2
    locV := fun i P w => D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P }) w
    satV := fun i P w => D.nbc.satAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P }) w
    locV_unr := fun i P w => haveI := hfin i; _root_.GlobalTheory.T.galois_family_irreducible_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) P w
    pt_loc := fun i P x hx w hw => haveI := hfin i; _root_.GlobalTheory.T.galois_family_trace_frobenius_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) (ptV i) (hptV i) P x hx w hw
    infWt := fun i => D.nbc.infW (X.nd.j i) (A.au.clsWt (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 (b i))
    locW := fun i σ w => A.row.locR σ w
    satW := fun i σ w => A.row.satR σ w
    lab_loc := fun i k σ v => A.row.lab_eq k σ v
    wdOf := fun i {a} r w => A.wd.wdOf (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_dim := fun i {a} r w => A.wd.wdOf_dim (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_unr := fun i {a} r w => A.wd.wdOf_unr (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_frob := fun i {a} r w => A.wd.wdOf_frob (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_ine := fun i {a} r w => A.wd.wdOf_ine (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_mono0 := fun i {a} r w => A.wd.wdOf_mono0 (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsCrysW := fun i {a} r w => A.wd.IsCrysW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsPotCrysW := fun i {a} r w => A.wd.IsPotCrysW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsdRW := fun i {a} r w => A.wd.IsdRW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    jumpsW := fun i {a} r τ => A.wd.jumpsW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r τ
    wdOf_unrL := fun i {a} r w => A.wd.wdOf_unrL (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_mono0L := fun i {a} r w => A.wd.wdOf_mono0L (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    jumpsInf := fun i {a} π τ => (D.naut.infG π ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp τ)).map (GlobalTheory.AutPart.jumpOf a)
    locAutHodgeTateWeightsLevelZero := fun i τ => (D.nbc.infW (X.nd.j i) (A.au.clsWt (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 (b i))
      ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp τ)).map (GlobalTheory.AutPart.jumpOf D.R.nV)
    jumpsInf_def := fun i {a} π τ h => by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun z hz => GlobalTheory.AutPart.jumpOf_spec a z (hralg π _ h z hz)
    locAut_hodgeTateWeightsLevelZero_def := fun i τ => by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun z hz => GlobalTheory.AutPart.jumpOf_spec _ z ((D.nbc.infW_alg _ _ _).2 z hz)
    chi_mu := fun i w hw => _root_.GlobalTheory.T.galois_family_hecke_compatible_alt hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i (μ i) (hμc i) (hμ i) w hw
    kFbar := κ }, {
    embAV := fun i P => (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P })
    embAV_inj := fun i P P' h => hinj i P P' ((A.au.iso _ _ _ _ _).1 h).2
    embAV_loc := fun _ _ _ => rfl
    embAV_sat := fun _ _ _ => rfl
    embAV_sph := fun i P w hw => haveI := hfin i; _root_.GlobalTheory.SphNonSplit.sphAU_of_not_split_m_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) P w hw
    embAV_inf := fun i P => by
      exact (congrArg (D.nbc.infW (X.nd.j i)) (A.au.wt _ _ _ _ (b i) (hb i).1)).symm }, ⟨{
    iotaQ := fun _ => rfl
    iotaQC := fun _ => rfl
    kFbar := hκ
    locW := fun _ _ _ => rfl
    satW := fun _ _ _ => rfl
    wdOf := fun _ _ _ _ => ⟨rfl, Iff.rfl, Iff.rfl, Iff.rfl, fun _ => rfl⟩
    muC := hμ
    S := F
    irr := irr
    inj := hinj
    surj := hsurj
    typeV := fun _ _ => rfl
    ptV := hptV
    emb := fun _ _ => rfl }⟩⟩
end
end
