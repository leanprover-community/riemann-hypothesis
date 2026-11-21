import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepInducedMatches

section
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_iotaOQ' : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) := by
  first | exact @GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data | exact GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data | (intros; apply GlobalTheory.CoeffEmbedding.continuous_iotaOQ_of_data <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_galois_rep_decomposition_induced : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (c : ↥(Dec (F := E) A) →* GL (Fin 1) (Om l)), IsPstAt P Bw r → IsPstAt P Bw c → ∀ v : Fin a → Om l, v ≠ 0 → (∀ g, (r g : Matrix (Fin a) (Fin a) (Om l)).mulVec v = (c g : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 • v) → ∀ σ : ↥(Weil h), (WD.charPol (wdAt P ι Bw h hj c) σ).roots ≤ (WD.charPol (wdAt P ι Bw h hj r) σ).roots := by
  first | exact @GlobalTheory.PstLine.roots_charPol_le | exact GlobalTheory.PstLine.roots_charPol_le | (intros; apply GlobalTheory.PstLine.roots_charPol_le <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_galois_rep_induced_matches : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (c : ↥(Dec (F := E) A) →* GL (Fin 1) (Om l)), IsPstAt P Bw r → IsPstAt P Bw c → ∀ v : Fin a → Om l, v ≠ 0 → (∀ g, Matrix.vecMul v (r g : Matrix (Fin a) (Fin a) (Om l)) = (c g : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 • v) → ∀ σ : ↥(Weil h), (WD.charPol (wdAt P ι Bw h hj c) σ).roots ≤ (WD.charPol (wdAt P ι Bw h hj r) σ).roots := by
  first | exact @GlobalTheory.Pst.QuotLine.quotient_char_eig | exact GlobalTheory.Pst.QuotLine.quotient_char_eig | (intros; apply GlobalTheory.Pst.QuotLine.quotient_char_eig <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.Pst GlobalTheory.WeilDeligne

namespace GlobalTheory.LocalInv

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def PstTie (T : GlobalTheory.RowTie.WDTie N A) : Prop :=
  ∃ (P : ∀ i, LocPrime (N.l i)) (AI : ∀ i, LocAinf (N.l i) (P i)) (_ : ∀ i, Nonempty (LocTied (N.l i) (P i) (AI i)))
    (LL : ∀ i, FinExt (N.l i))
    (br : ∀ i (w : PlE H), w ∈ placesOver H.E (N.l i) →
      LocBridge (N.l i) H.E N.Om (Dec (F := H.E) (N.plOm.1 w)) ↥(OL (LL i)))
    (hj : ∀ i w hw, Induces (br i w hw)),
    ∀ (i : N.Loc) {a : ℕ} (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) (w : PlE H)
      (hw : w ∈ placesOver H.E (N.l i)),
      Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
      A.IsdRW i r w →
      IsdRAt (P i) (br i w hw) (resDec N.plOm.1 r w) ∧
        T.e w (A.wdOf i r w) = wdAt (P i) (A.iotaQC i) (br i w hw) (N.plOm.2 w) (hj i w hw) (resDec N.plOm.1 r w)

theorem cont_mapRep_iotaOQ (i : N.Loc) {b : ℕ} (τ : G H.E N.Om →* GL (Fin b) (N.O i)) (hτ : Cont N i τ) :
    Continuous (fun g => ((mapRep (iotaOQ N A i) τ g : GL (Fin b) (Qbar (N.l i))) :
      Matrix (Fin b) (Fin b) (Qbar (N.l i)))) :=
  continuous_matrix fun p q => (GlobalTheory.T.continuous_iotaOQ' N A i).comp (hτ.matrix_elem p q)

end GlobalTheory.LocalInv
end
end
