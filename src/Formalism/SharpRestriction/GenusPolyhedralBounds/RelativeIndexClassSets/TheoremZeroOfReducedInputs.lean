import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroBundledOfLift
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyZeroChoice
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyQuotientBounded

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def zAll (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (T : ℕ) : Set (Rp X la G.N) :=
  {v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j (X.wF0 wL wF)), ∑ i, al i = a0 D j T ∧
      θ ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ v = secPow X la G.w al * emb X la G.N (X.inc _ θ)}

def InContainMR (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ) : Prop :=
  Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc ka F)) '' (WeightFamilies.MggK B CRm T c j ka : Set (B.Cusp j ka))) ≤
    Submodule.span (Kp X la G.N)
      ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
          v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
       zAll G la S T)

def ShareRhoR (G : GlobalFamilyData X ka wL wF) (S : Scal B) (T d : ℕ) : Prop :=
  ∀ la, (finrank (Kp X la G.N) ↥(Submodule.span (Kp X la G.N) (zAll G la S T)) : ℝ) ≤
    22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def GrowthConstantBound (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (Gc : ℝ) : Prop :=
  ∀ po ∈ ({D.host.pde, D.host.pde'} : Set ℕ), Formalism.MainNotions.WeightAlgebra.Gc large₂ B (1009 * Zb D large₂) po ≤ Gc

def PageGq (large₂ : SizeData₂ D) (Gc Ch Ah : ℝ) : Prop := Gc ≤ WeightFamilies.PPv D large₂ Ch Ah

def Conclusion1OfCombR : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ) (Qf : ∀ la, LocalPointData G la),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd →
    GrowthConstantBound large₂ B Gc → PageGq large₂ Gc Ch Ah →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoR G S T ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T (WeightFamilies.rhoP B K.CRm T (cc D large₂ C2 A2 CR wL) j ka) ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    (∀ la, InBasis G la) → (∀ la, (Qf la).InCurve) → (∀ la, (Qf la).InTie S) → (∀ la, (Qf la).InLiftC S Gc Prw T) →
    (∀ la, InContainMR G la S K.CRm T (cc D large₂ C2 A2 CR wL)) →
    CombBound G S (cc D large₂ C2 A2 CR wL) nus →
    Heights Qf Gc PH Prw Pet →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

def GlobalFamilyData.setZQ (G : GlobalFamilyData X ka wL wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
    (th0 : Fin rz → B.Cusp j (X.wF0 wL wF))
    (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G.N) →₀ ℕ) →₀ B.Cusp j ka) (rq : ℕ) (th : Fin rq → B.Mlat j ka) :
    GlobalFamilyData X ka wL wF :=
  { G with rz := rz, alz := alz, th0 := th0, zc := zc, rq := rq, th := th }

section Tr

variable (G : GlobalFamilyData X ka wL wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
    (th0 : Fin rz → B.Cusp j (X.wF0 wL wF))
    (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G.N) →₀ ℕ) →₀ B.Cusp j ka) (rq : ℕ) (th : Fin rq → B.Mlat j ka)

def LocalPointData.tr {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) : LocalPointData (G.setZQ rz alz th0 zc rq th) la :=
  ⟨Q.y, Q.g0, Q.c⟩





theorem tr_InLiftC {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (S : Scal B) (Gc Prw : ℝ) (T : ℕ) (h : Q.InLiftC S Gc Prw T) :
    (Q.tr G rz alz th0 zc rq th).InLiftC S Gc Prw T := h


theorem tr_CombBound (S : Scal B) (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (h : CombBound G S c nus) :
    CombBound (G.setZQ rz alz th0 zc rq th) S c nus := h






end Tr

theorem ShortG.mono {w : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)} {β β' : ℝ} (h : ShortG X w N β) (hb : β ≤ β') :
    ShortG X w N β' := by
  unfold ShortG at h ⊢
  obtain ⟨Sh, h1, h2, h3⟩ := h
  exact ⟨Sh, h1, h2, fun g hg => (h3 g hg).trans hb⟩

theorem exists_prime (K : Type) [Field K] [NumberField K] : Nonempty (HeightOneSpectrum (𝓞 K)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 K)
  exact ⟨⟨M, hM.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField K)⟩⟩

private theorem size_nonneg_lemma (w : WeightFamilies.Wt D j) : 0 ≤ w.size := by
  unfold WeightFamilies.Wt.size
  positivity

theorem shortG_of_scalB {large₂ : SizeData₂ D} {C1 A1 : ℝ} {S : Scal B} {T : ℕ} {Gc : ℝ}
    (hS : ScalB large₂ X C1 A1 S ka wL wF T) (hG : GrowthConstantBound large₂ B Gc) :
    ShortG X (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF)) (Gc * (X.wF0 wL wF).size) ∧
      ShortG X ka (X.Thc S.sK ka) (Gc * ka.size) := by
  obtain ⟨-, -, -, -, -, po, hpo, -, PLam, hPL, -, -, hs0, hsK⟩ := hS
  have hG' := hG
  unfold GrowthConstantBound at hG'
  have hle : Formalism.MainNotions.WeightAlgebra.Gc large₂ B PLam po ≤ Gc := by
    refine le_trans ?_ (hG' po hpo)
    unfold Formalism.MainNotions.WeightAlgebra.Gc
    linarith
  exact ⟨ShortG.mono hs0 (mul_le_mul_of_nonneg_right hle (size_nonneg_lemma _)),
    ShortG.mono hsK (mul_le_mul_of_nonneg_right hle (size_nonneg_lemma _))⟩

theorem inContainM_of (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ)
    (hM : InContainMR G la S CRm T c) (hZ : InContainZ G la S T) : InContainM G la CRm T c := by
  refine le_trans hM ?_
  rw [Submodule.span_le]
  rintro v (hv | hv)
  · exact Submodule.subset_span (Or.inl hv)
  · have h1 : v ∈ Submodule.span (Kp X la G.N) (Set.range (zK G la)) :=
      hZ (Submodule.subset_span hv)
    exact Submodule.span_mono Set.subset_union_right h1


end Formalism.MainNotions.Gaps.EtaleWeightGaps
