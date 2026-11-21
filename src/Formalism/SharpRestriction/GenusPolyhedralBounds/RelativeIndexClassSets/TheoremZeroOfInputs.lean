import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfRefinedInputs

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

section Inputs

variable {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def AtMBasis (G : GlobalFamilyData X ka wL wF) : Prop := ∀ la, InBasis G la

def AtMCurve {G : GlobalFamilyData X ka wL wF} (Qf : ∀ la, LocalPointData G la) : Prop := ∀ la, (Qf la).InCurve

def AtMTie {G : GlobalFamilyData X ka wL wF} (Qf : ∀ la, LocalPointData G la) (S : Scal B) : Prop := ∀ la, (Qf la).InTie S

def AtMLift {G : GlobalFamilyData X ka wL wF} (Qf : ∀ la, LocalPointData G la) (S : Scal B) (Gc Prw : ℝ) (T : ℕ) : Prop :=
  ∀ la, (Qf la).InLiftC S Gc Prw T

def AtMInputs (G : GlobalFamilyData X ka wL wF) (S : Scal B) (T : ℕ) (Gc PH Prw Pet : ℝ) : Prop :=
  ∃ Qf : ∀ la, LocalPointData G la,
    AtMBasis G ∧ AtMCurve Qf ∧ AtMTie Qf S ∧ AtMLift Qf S Gc Prw T ∧ Heights Qf Gc PH Prw Pet




end Inputs


def Conclusion1OfComb5 : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd4 (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoT (D := D) (j := j) T G.rz G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom4 (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    (∀ la, InContainZ G la S T) → (∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL)) →
    (j < D.R.m → ∃ Qf : ∀ la, LocalPointData G la,
      (∀ la, InBasis G la) ∧ (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw T) ∧
      CombBound4 G Qf S (cc D large₂ C2 A2 CR wL) nus ∧ Heights Qf Gc PH Prw Pet) →
    (D.R.m ≤ j → DepthAtM (X j h1 h2) S wL nus) →
    (D.R.m ≤ j → AtMInputs G S T Gc PH Prw Pet) →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)


end Formalism.MainNotions.Gaps.EtaleWeightGaps
