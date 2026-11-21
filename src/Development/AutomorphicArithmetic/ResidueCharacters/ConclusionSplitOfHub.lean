import Mathlib
import Development.AutomorphicArithmetic.ResidueCharacters.ExistsUnion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftColumnRowSetup
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JumpWindow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankLeOfSubsetClosureRange
import Formalism.SharpRestriction.LevelLetterCocycles.JumpAndLengthOfAdmitted
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExpone
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientSubContinuitySetup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedPlacesDeclared
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCaseBoundAtPointOfAdmittedItems

section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
open Module GlobalTheory.LiftExpSplit

namespace UpperTheory.N

variable {D : D7}

theorem liftAt_of_liftK (i : D.nd.Loc) (N : ℕ) (hK : LiftK (D.loc (D.nd.l i))) (hC : CycAt N i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    {ι : Type} {k : ℕ} (Ms : ι → Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1)
    (hc : ∀ x v, Continuous fun g => (Ms x g).mulVec v)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL)) (h : ℕ)
    (hcr : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)))
    (hS : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)) τ (Set.Icc (-(h : ℤ)) h)) :
    LiftAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (fun x : ι => ⇑(Ms x)) (eL (D.nd.l i) N h) := by
  intro V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 L1 hc1 hs1 V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 L2 hc2 hs2 F hF'
  let T₁ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V1, ρ := ρ1, cont := hc1, L := L1 }
  let T₂ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V2, ρ := ρ2, cont := hc2, L := L2 }
  obtain ⟨hcr1, hj1⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(h : ℤ)) h) hcr hS T₁ hs1
  obtain ⟨hcr2, -⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(h : ℤ)) h) hcr hS T₂ hs2
  exact hK N h (D.nbr i w hw).Kw C.LL (hC w hw C) T₁ T₂ F hcr1 hcr2 hF' hj1

theorem lift_exponent_admissible_cols_rows_of_crystalline (L : SizeData₂ D) (i : D.nd.Loc) (N : ℕ) (hK : LiftK (D.loc (D.nd.l i))) (hC : CycAt N i)
    (X : KillingConditions.HubData D) (dc : TruncatedSeriesCountingIdentities.Decl D i) (hgood : ∀ i, GoodR D.nd i (X.r i)) (ep : Bool) (hA : AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep)
    (he : AdmissibleParameterJ.JumpAbsoluteBound L) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i)
    (hT : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) x,
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))))
    (hD : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) x,
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x)))) :
    EmbeddingTypes.LiftExponentColumn i (X.r i) dc (eL (D.nd.l i) N (Formalism.MainNotions.N.hN L)) ∧
      EmbeddingTypes.LiftExponentDualPlaces i (X.r i) dc (eL (D.nd.l i) N (Formalism.MainNotions.N.hN L)) := by
  have hcont : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (X.r i) := continuous_family_of D i (X.r i) (hgood i)
  have hj := D.nd.j_range i
  have hhB : AdmissibleParameterJ.hJ L + 2 = Formalism.MainNotions.TwistedPlaces.hB L := by
    unfold AdmissibleParameterJ.hJ Formalism.MainNotions.TwistedPlaces.hB; ring

  have hwinT : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((a : ℚ) : ℝ)) = (a : ℝ) := by push_cast; rfl
    rw [hc] at hb
    linarith
  have hwinD : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) τ,
      JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))) τ
        (Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L)) := by
    intro w hw C x τ a ha
    obtain ⟨g, ρ, -, hx, -⟩ := hA i (X.r i) (hgood i) w hw C τ
    have hq := (hx x a).2.2.1.mp ha
    have hb := he.1 (D.nd.j i) hj.1 hj.2 ρ _ _ hq
    have hb2 := he.2.1
    apply mem_window L a
    have hc : (((-(a : ℚ) - 1 : ℚ)) : ℝ) = -(a : ℝ) - 1 := by push_cast; rfl
    rw [hc] at hb
    rw [abs_le] at hb ⊢
    constructor <;> linarith [hb.1, hb.2]
  refine ⟨?_, ?_⟩
  · intro w hw _ C _
    exact liftAt_of_liftK i N hK hC w hw C (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rTwO_cont D i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (hT w hw C) (fun x => hwinT w hw C x)
  · intro w hw _ C _
    exact liftAt_of_liftK i N hK hC w hw C (fun x => TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))
      (fun x v => locC_cont D i _ (rDuO_cont i (X.r i) hcont x) w hw C v) (hFont w hw C)
      (Formalism.MainNotions.N.hN L) (hD w hw C) (fun x => hwinD w hw C x)

end UpperTheory.N

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

variable {D : D7}

theorem block_condition_at_places_of_jump_window (i : D.nd.Loc) (N : ℕ) (hK : TBK (D.loc (D.nd.l i))) (hC : CycAt N i)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (h : ℕ) (ht : D.R.t ≤ h)
    (hJ : GlobalTheory.BlockWindow.JumpWindow D i r π h) :
    TruncatedSeriesCountingIdentities.admTB i r π (cBL (D.nd.l i) N h (4 * D.R.n * D.R.nV) D.R.t) := by
  intro w hw C _
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) ≤ 4 * D.R.n := by
    rw [GlobalTheory.HubLoc.card_emb _ _ fun τ x => C.le ((D.nbr i w hw).LL_split τ x)]
    exact GlobalTheory.bridge_finrank_le D i w hw
  haveI : Finite (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) := by
    haveI := (D.nbr i w hw).Kw.2
    infer_instance
  obtain ⟨U, h1, h2, h3⟩ := exists_union (4 * D.R.n) D.R.nV h hcard
    (fun τ a => IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) τ a) (fun τ => by
      obtain ⟨U, a, b, c⟩ := hJ w hw C.LL C.le τ
      exact ⟨U, a, fun u hu => ⟨(b u hu).1, by have := (b u hu).2; omega⟩, c⟩)
  rw [GlobalTheory.BridgeInertia.inertEq D i w hw]
  exact hK N h _ D.R.t (D.nbr i w hw).Kw C.LL (hC w hw C) ht _ U h1 h2 (fun τ a ha => h3 τ a ha)

end UpperTheory.N

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

variable {D : D7}

def JumpsNoZero (i : D.nd.Loc) (M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) (h : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw),
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) ∧
    ∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1,
      (∃ U : Finset ℤ, U.card ≤ D.R.r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧
        ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a → a ∈ U) ∧
      ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ 0

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem kill_of (i : D.nd.Loc) (N : ℕ) (hK : InvariantsKilledOverCyclotomic (D.loc (D.nd.l i))) (hC : CycAt N i)
    (M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) (h : ℕ) (hM : JumpsNoZero i M h)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hc : ∀ v, Continuous fun g => matRep (TruncatedSeriesCountingIdentities.locC C M) g v)
    (L2 : Lattice (O := ↥(OL C.LL)) (matRep (TruncatedSeriesCountingIdentities.locC C M))) :
    ∀ x : (Fin D.R.r → ↥C.LL.1) ⧸ L2.T, (∀ g, actD L2 g x = x) →
      ((D.nd.l i : ↥(OL C.LL)) ^ c0L (D.nd.l i) N h (4 * D.R.n * D.R.nV)) • x = 0 := by
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) ≤ 4 * D.R.n := by
    rw [GlobalTheory.HubLoc.card_emb _ _ fun τ x => C.le ((D.nbr i w hw).LL_split τ x)]
    exact GlobalTheory.bridge_finrank_le D i w hw
  haveI : Finite (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) := by
    haveI := (D.nbr i w hw).Kw.2
    infer_instance
  obtain ⟨U, h1, h2, h3⟩ := exists_union (4 * D.R.n) D.R.r h hcard
    (fun τ a => IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a) (fun τ => ((hM w hw C).2 τ).1)
  have hn : U.card ≤ 4 * D.R.n * D.R.nV := h1.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
  exact hK N h _ (D.nbr i w hw).Kw C.LL (hC w hw C)
    { V := Fin D.R.r → ↥C.LL.1, ρ := matRep (TruncatedSeriesCountingIdentities.locC C M), cont := hc, L := L2 } U hn h2 (hM w hw C).1
    (fun τ a ha => h3 τ a ha) (fun τ => ((hM w hw C).2 τ).2)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem invariants_length_admissible_of_nonzero_jumps (i : D.nd.Loc) (N : ℕ) (hK : InvariantsKilledOverCyclotomic (D.loc (D.nd.l i))) (hC : CycAt N i)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (h : ℕ)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))
    (hM : JumpsNoZero i (T2O D.nd i ρ π) h) :
    EmbeddingTypes.H0ColumnLengthBound i ρ π dc (fun _ => c0L (D.nd.l i) N h (4 * D.R.n * D.R.nV)) := by
  intro _ u _ w hw _ C _ L2 hstd
  have hT2c : Continuous fun g => T2O D.nd i ρ π g := GlobalTheory.HTW.RecS.Model.continuous_twistedDual_rhoO i ρ π hρ
  have hc : ∀ v, Continuous fun g => matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) g v :=
    fun v => (GlobalTheory.CrysChiOne.locC_cont' C _ hT2c).matrix_mulVec continuous_const
  have hkill := kill_of i N hK hC _ h hM w hw C hc L2
  unfold EmbeddingTypes.lenInvD
  haveI : IsDiscreteValuationRing ↥(OL C.LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr C.LL
  haveI : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := Formalism.BasicNotions.Examples₂.LB.OL_frac C.LL
  refine EmbeddingTypes.len_le_of_kill (Br.PD D.loc D.nbr i w hw) L2.T hstd _ _ ?_
  intro x hx
  rw [Br.PD_p]
  exact hkill x fun g => hx g

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem length_invariants_Wprime_divisible_le_of_nonzero_jumps (i : D.nd.Loc) (N : ℕ) (hK : InvariantsKilledOverCyclotomic (D.loc (D.nd.l i))) (hC : CycAt N i)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (h : ℕ)
    (hW : Continuous fun g => WpO D.nd i ρ π g) (hM : JumpsNoZero i (WpO D.nd i ρ π) h)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)) :
    (Br.h0W i u ρ π : ℝ) ≤ (D.R.r : ℝ) * (c0L (D.nd.l i) N h (4 * D.R.n * D.R.nV) : ℕ) := by
  let C := TruncatedSeriesCountingIdentities.CoefExt.self i u hu
  have e : TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π) = Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)) := by
    ext g a b
    rfl
  have hc : ∀ v, Continuous fun g => matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π)) g v :=
    fun v => (GlobalTheory.CrysChiOne.locC_cont' C _ hW).matrix_mulVec continuous_const
  have hkill := kill_of i N hK hC _ h hM u hu C hc
  rw [e] at hkill
  have hK' := GlobalTheory.LengthH0Bound.inv_killed (D.nbr i u hu) (WpO D.nd i ρ π) (decS D.nd u) (D.nd.l i) _
    (hkill (Br.lat (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))))
  have hq := GlobalTheory.LengthH0Bound.lenUnit_le_of_kill D.R.r (D.nd.l i) _ (GlobalTheory.LengthH0Bound.natCast_ne_zero (D.nbr i u hu)) _ hK'
  exact_mod_cast hq

end UpperTheory.N

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
open GlobalTheory.NLink.AmbSub

namespace UpperTheory.N

theorem amb_of_setPt {D : D7} (i : D.nd.Loc) (X : KillingConditions.HubData D) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (hS : SetPt i (X.r i) (X.ρ i) π)
    (hρ : Continuous fun g => ((X.ρ i π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :
    EmbeddingTypes.ambSub i (X.r i) π dc ∧ EmbeddingTypes.ambCont i (X.r i) (X.ρ i) π ∧ EmbeddingTypes.ColumnH0Vanishing i (X.ρ i) π dc := by
  obtain ⟨_, hG2, _, _, _, _, _, _, hCont, _, _, _, _, _, hFont, _, _⟩ := hS
  have hcx : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) (v : Fin D.R.nV → ↥C.LL.1),
      Continuous fun g => (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x) g).mulVec v :=
    fun w hw C x v => locC_cont D i _ (rTwO_cont D i (X.r i) hCont x) w hw C v
  have hcr : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) := by
    intro w hw C x
    rw [locC_rTwO]
    exact (hG2 w hw C).2 x
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ w hw _ C A hA
    have hJ : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x))) τ
        {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) π))) τ a} := by
      intro x τ
      refine jumps_of_multV_eq (O := ↥(OL C.LL)) (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C)
        (hFont w hw C) x π (hcr w hw C x) (hcr w hw C π) τ (fun a => ?_)
      rw [locC_rTwO, locC_rTwO]
      exact (hG2 w hw C).1.2.1 τ x π a
    exact subsum_crys (fun x => TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i (X.r i) x)) (hcx w hw C) (hFont w hw C)
      (hcr w hw C) hJ A hA
  · intro w hw C
    refine ⟨fun x v => hcx w hw C x v, fun _ => ⟨fun v => ?_, fun v => ?_⟩⟩
    · exact locC_cont D i _ (WpO_cont i (X.ρ i) π hρ) w hw C v
    · exact locC_cont D i _ (GlobalTheory.TwistedDualLoc.continuous_T2O D i (X.ρ i) π hρ) w hw C v
  · intro _ w hw _ C
    exact (hG2 w hw C).1.2.2.2.2.2.1

end UpperTheory.N

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

open Classical in

def withDc {D : D7} (X : KillingConditions.HubData D) (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) : KillingConditions.HubData D :=
  { X with dc := Function.update X.dc i dc }

open Classical in
theorem withDc_dc {D : D7} (X : KillingConditions.HubData D) (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) : (withDc X i dc).dc i = dc := by
  simp only [withDc, Function.update_self]

theorem conclusion_split (Pr : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ) (S : Setup L nch HW X C₂)
    (i : D.nd.Loc) (hg : D.nd.l i ∉ TwistedPlaces.gset D) (N : ℕ) (hC : CycAt N i) (hL : EmbeddingTypes.hypL i)
    (hdecl : ∀ ep, (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.ambTypeD (D := D) i ep)
    (hK : LiftK (D.loc (D.nd.l i)) ∧ InvariantsKilledOverCyclotomic (D.loc (D.nd.l i)) ∧ TBK (D.loc (D.nd.l i))) :
    ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.RowsAreConj i dc ∧ ∀ π ∈ D.nd.Zgood i,
      EmbeddingTypes.ShaBoundTheoremB i (X.ρ i) π dc (eL (D.nd.l i) N (Formalism.MainNotions.N.hN L))
        (fun _ => c0L (D.nd.l i) N (GlobalTheory.HubX.hOf L) (4 * D.R.n * D.R.nV))
        (cBL (D.nd.l i) N ⌊2 * L.sc.b⌋₊ (4 * D.R.n * D.R.nV) D.R.t) ∧
      (∀ u ∈ dc.col, (Br.h0W i u (X.ρ i) π : ℝ) ≤
        (D.R.r : ℝ) * (c0L (D.nd.l i) N (GlobalTheory.HubX.hOf L) (4 * D.R.n * D.R.nV) : ℕ)) ∧
      ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1 := by
  have fa := S.facts
  have hAJ : AdmissibleParameterJ.AdmJ L := fa.admJ L S.par
  have hJ : AdmissibleParameterJ.JumpConditions L := GlobalTheory.JumpStatement.holds_all D L hAJ
  have hJ' := hJ
  obtain ⟨⟨ep, hep⟩, hJb, hJc, -, hJe, hJf, -⟩ := hJ'
  have hfam := S.canon.fam
  have hg0 : D.nd.l i ≠ D.host.g 0 := hL.2.2.2.1
  have hg1 : D.nd.l i ≠ D.host.g 1 := hL.2.2.2.2
  obtain ⟨⟨dc, hdc⟩, hType⟩ := hdecl ep
  refine ⟨dc, hdc.2, fun π hπ => ?_⟩
  have hZ : π ∈ D.nd.Z i := LargeLevelLemmas.zgoodSubsetZ i hπ
  have sp := GlobalTheory.T.set_point_good Pr D L P nch HW F Cm X C₂ S i hg π hπ
  have hρ := hfam.cont i π
  obtain ⟨sub, acont, a56⟩ := amb_of_setPt i X π dc sp hρ
  obtain ⟨g1, g2, g3, g4, _, g5x, g6, bk, cont, ss, dec, eps, tie, shape, font, hH2, cft⟩ := sp
  have hG2 := GlobalTheory.T.admG2_twist_setup Pr D L P nch HW F Cm X C₂ S ep hep i
  have hG5 := GlobalTheory.T.admG5_setup Pr D L P nch HW F Cm X C₂ S i hg π hπ
  have hcr := GlobalTheory.T.decomposition_local_away D i (X.r i) (X.ρ i) π fa.Conclusion1.1 font (hfam.good i) hρ dec hg0 hg1
  have hjp := GlobalTheory.T.decomposition_local_above D L ep hep hJb hJc hJe hJf i (X.r i) (X.ρ i) π (hfam.good i) hZ dec
  have hW : JumpsNoZero i (WpO D.nd i (X.ρ i) π) (GlobalTheory.HubX.hOf L) :=
    fun w hw C => ⟨(hcr w hw C).2.2.1, fun τ => hjp w hw C τ _ (Or.inl rfl)⟩
  have hT2 : JumpsNoZero i (T2O D.nd i (X.ρ i) π) (GlobalTheory.HubX.hOf L) :=
    fun w hw C => ⟨(hcr w hw C).2.2.2, fun τ => hjp w hw C τ _ (Or.inr rfl)⟩
  obtain ⟨lc, lr⟩ := lift_exponent_admissible_cols_rows_of_crystalline L i N hK.1 hC X dc hfam.good ep hep hJe font
    (fun w hw C x => (hG2 hg0 hg1 w hw C).2.1 x) (fun w hw C x => (hcr w hw C).2.1 x)
  have hH0 := invariants_length_admissible_of_nonzero_jumps i N hK.2.1 hC (X.ρ i) π dc _ hρ hT2
  obtain ⟨ht, hWin⟩ := GlobalTheory.T.hodgeTateJumpWindow_of_jumpSets D L hJ S.par67
  have tb9 := block_condition_at_places_of_jump_window i N hK.2.2 hC (X.r i) π _ ht (hWin i (X.r i) (hfam.good i) π)
  have tb : EmbeddingTypes.admTB i (X.r i) π dc _ := fun w hw _ C hC' => tb9 w hw C hC'
  obtain ⟨l51, l52, _⟩ := GlobalTheory.charpoly_span_and_hom_relations_of_admissible D i (X.r i) (X.ρ i) π g1
  have h78 := GlobalTheory.T.ambient_conditions_at_good Pr.font D L (withDc X i dc) fa.g2.1 hJ.1 hJc hfam i hg π hπ
  rw [withDc_dc] at h78
  have hcB : ∀ k, GlobalTheory.HubLoc.cBnum (D.nd.l k) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ (withDc X i dc).cB k := by
    intro k
    show _ ≤ X.cB k
    rw [S.canon.cB]; exact le_rfl
  have hCl := GlobalTheory.closingFamilyX Pr.font Pr.fin D HW F L (withDc X i dc)
    (fun L' h => GlobalTheory.JumpStatement.holds_all D L' h) hAJ S.par67 fa.Conclusion1.1 fa.large.2.1 hfam hcB
  have dual := hCl.2.2.1 i hg π hπ
  have h1f := hCl.2.2.2 i π
  rw [withDc_dc] at dual h1f
  have a51 := GlobalTheory.T.admissibleAtGoodPoints_of_coefRing_taken_at_live GlobalTheory.Published.cheb_holds D X fa.large.2.2 (GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred D fa.rhoBar) hfam i π hπ
  have bka : LargeLevelLemmas.BlochKatoAnnihilators i := GlobalTheory.T.blochKatoAnnihilator_all_of_tateDuality_eulerChar Pr.bk Pr.tate Pr.euler D i
  have fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i := GlobalTheory.T.tateFinitenessAll_of_localTateDuality Pr.tate D i
  have hA : EmbeddingTypes.admitted i (X.r i) (X.ρ i) π dc ep _ _ _ :=
    ⟨g1, hG2, g3, g4, hG5, g5x, g6, a56, a51, l51, l52, ⟨bk, bka⟩, lc, lr, hH0, tb, GlobalTheory.T.unramifiedTrivialH1f_of_decl D i dc, cont, ss, dec, eps,
      tie, shape, font, hH2, fin, cft, h78.2.2.2, dual, h78.1, h78.2.1, h78.2.2.1, h1f, sub, acont, hType⟩
  obtain ⟨-, -, hB⟩ := GlobalTheory.T.splitCase_bound_at_point_of_admitted_items_alt Pr.artin Pr.tate Pr.euler D i (X.r i) (X.ρ i) π dc ep _ _ _ hA (fun _ _ _ => g2) hL hdc hZ
  exact ⟨hB, fun u hu => length_invariants_Wprime_divisible_le_of_nonzero_jumps i N hK.2.1 hC (X.ρ i) π _ (GlobalTheory.NLink.AmbSub.WpO_cont i (X.ρ i) π hρ) hW u
    ((dc.cover u).1 (Or.inr hu)), fun v hv => (g5x v (Or.inr hv)).2.2.1 hv⟩

end UpperTheory.N

end
end
