import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PDgFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCpFacts
import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PEigSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSplitLine
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSSLeft
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PContLeft
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamWeightDirectSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSumDR
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwJumps
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PTwLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PWDFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PFrobSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistableStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.MetAndHolds
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsFurther
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatPol
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PAtPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotentiallySemistable
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.AlgebraicCharacterWD
import Development.WeilBound.CoreStatements.PublishedTheorems.HeckeLAdicCharacters.Outright
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.eigTransfer_holds :
    EigTransfer := by
  intro Γ k _ _ _ _ N N' ρ ρ' hρ hρ' hcp c ⟨v, hv0, hv⟩
  have hN : N = N' := by
    have h := congrArg Polynomial.natDegree (hcp 1)
    simpa [cp, Matrix.charpoly_natDegree_eq_dim] using h
  subst hN
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ ρ' hρ hρ' (fun g => hcp g)
  refine ⟨(P : Matrix (Fin N) (Fin N) k).mulVec v, ?_, ?_⟩
  · intro h
    apply hv0
    have := congrArg (((P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec) h
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  · intro g
    have hg : ρ g * P = P * ρ' g := by
      rw [hP g]
      group
    have hm : (ρ g : Matrix (Fin N) (Fin N) k) * P = P * ρ' g := by
      rw [← Units.val_mul, hg, Units.val_mul]
    rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.peelOne_holds :
    DgFacts → CpFacts → EigTransfer → EigSum → SplitLine → SSLeft → PeelOne := by
  intro hDg hCp hTr hEig hSplit hSS Γ k _ _ _ _ m m' t t' r r' a a' hr hr' hne hcp
  set c := a (Fin.last t) with hc
  have hR1 : IsSSRep (sumRep r (dg a')) := GlobalTheory.BCGal.ss_sumRep _ _ hr (hDg Γ k t' a').1
  have hR2 : IsSSRep (sumRep r' (dg a)) := GlobalTheory.BCGal.ss_sumRep _ _ hr' (hDg Γ k (t + 1) a).1
  have hcpR : ∀ g, cp (sumRep r (dg a')) g = cp (sumRep r' (dg a)) g := by
    intro g
    rw [(hCp Γ k (m + 1) t').1, (hCp Γ k m' (t + 1)).1, (hDg Γ k t' a').2, (hDg Γ k (t + 1) a).2]
    exact hcp g
  have hv2 := (hEig Γ k m' (t + 1) r' a c).1 ⟨Fin.last t, rfl⟩
  have hv1 := hTr Γ k _ _ (sumRep r (dg a')) (sumRep r' (dg a)) hR1 hR2 hcpR c hv2
  have hv := (hEig Γ k (m + 1) t' r a' c).2 (fun j h => hne (Fin.last t) j h.symm) hv1
  obtain ⟨s, hs⟩ := hSplit Γ k m r hr c hv
  have hsum : IsSSRep (sumRep s (rk1 c)) := (hSS Γ k (m + 1) 0).2.1 r _ hs hr
  refine ⟨s, (hSS Γ k m 1).1 s (rk1 c) hsum, hs, ?_⟩
  intro g
  have h1 : cp r g = cp s g * (X - C ((c g : kˣ) : k)) := by
    rw [← (hCp Γ k (m + 1) 0).2.2 r _ hs g, (hCp Γ k m 1).1, (hCp Γ k m 1).2.1]
  have h2 : lin a g = lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k)) := by
    simp only [lin]
    rw [Fin.prod_univ_castSucc]
  have hX : (X - C ((c g : kˣ) : k) : k[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have key := hcp g
  rw [h1, h2] at key
  apply mul_right_cancel₀ hX
  calc cp s g * lin a' g * (X - C ((c g : kˣ) : k))
      = cp s g * (X - C ((c g : kˣ) : k)) * lin a' g := by ring
    _ = cp r' g * (lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k))) := key
    _ = cp r' g * lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k)) := by ring
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Formalism.MainNotions.SumRepresentations.At (sumRep)

namespace UpperTheory.Gal.TP.Sub

theorem denseId_holds : CpFacts → DgFacts → DenseId := by
  intro _ _ Γ _ _ l _ m m' t t' r r' a a' hr hr' ha ha' D hD hEq g
  apply Polynomial.funext
  intro x
  have key : ∀ {n : ℕ} (s : Γ →* GL (Fin n) (Qbar l)), Continuous s →
      Continuous fun g => (cp s g).eval x := by
    intro n s hs
    simp only [cp, Matrix.eval_charpoly]
    exact (continuous_const.sub (Units.continuous_val.comp hs)).matrix_det
  have keyl : ∀ {n : ℕ} (b : Fin n → Γ →* (Qbar l)ˣ), (∀ i, Continuous (b i)) →
      Continuous fun g => (lin b g).eval x := by
    intro n b hb
    simp only [lin, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    exact continuous_finset_prod _ fun i _ =>
      continuous_const.sub (Units.continuous_val.comp (hb i))
  have h := Continuous.ext_on hD ((key r hr).mul (keyl a' ha')) ((key r' hr').mul (keyl a ha))
    (fun g hg => by
      simp only [Pi.mul_apply]
      rw [← Polynomial.eval_mul, ← Polynomial.eval_mul, hEq g hg])
  have hg := congrFun h g
  simp only [Pi.mul_apply] at hg
  rw [Polynomial.eval_mul, Polynomial.eval_mul]
  exact hg

end UpperTheory.Gal.TP.Sub

end
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.pstOfDR_holds :
    GlobalTheory.Published.DeRhamPotSemistable → PstOfDR := by
  intro hB l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r hr hd
  obtain ⟨T⟩ := hT
  exact hB.isPstAt T Bw r (Units.continuous_val.comp hr) hd
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.clTw_holds :
    FrobSub → TwLoc → TwJumps → PstOfDR → WDFacts → ContLeft → ClTw := by
  intro hF hL hJ hP hW hC E Ω _ _ _ _ _ l _ ι a s μ hs hμ w S c J m h1 h2
  refine ⟨fun hw => (hF E Ω l ι a w S c μ (h1.1 hw)).2 s (h2.1 hw), ?_⟩
  intro P AI hT A h O _ _ _ Bw hj
  obtain ⟨c1, d1, j1, p1⟩ := h1.2 P AI hT A h O Bw hj
  obtain ⟨c2, d2, j2, p2⟩ := h2.2 P AI hT A h O Bw hj
  have e1 : (rk1 μ).comp (Dec (F := E) A).subtype = rk1 (μ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw s μ).comp (Dec (F := E) A).subtype =
      tw (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  have e3 : Formalism.MainNotions.SumRepresentations.At.twGL (s.comp (Dec (F := E) A).subtype)
      (Matrix.GeneralLinearGroup.det.comp (rk1 (μ.comp (Dec (F := E) A).subtype))) =
      tw (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype) := by
    have hdet : Matrix.GeneralLinearGroup.det.comp (rk1 (μ.comp (Dec (F := E) A).subtype))
        = μ.comp (Dec (F := E) A).subtype := by
      ext g
      simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
    rw [hdet]
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, UpperTheory.V.Af.tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  rw [e1] at c1 d1 j1 p1
  rw [e2]
  have cs : Continuous (s.comp (Dec (F := E) A).subtype) := hs.comp continuous_subtype_val
  have cμ : Continuous (μ.comp (Dec (F := E) A).subtype) := hμ.comp continuous_subtype_val
  have ck := (hC _ (Qbar l) 1 1).2.2.2 _ cμ
  have ct := (hC _ (Qbar l) a 1).2.2.1 _ _ cs cμ
  obtain ⟨l1, l2⟩ := hL l P AI hT E Ω A O Bw a (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype)
  have dt := l1 d2 d1
  refine ⟨l2 c2 c1, dt, ?_, ?_⟩
  · intro τ LL' τ' hi
    exact hJ l P AI hT E Ω A O Bw a _ _ cs cμ τ (J τ) (m τ) (j2 τ LL' τ' hi) (j1 τ LL' τ' hi)
  · intro g
    have q1 := hP l P AI hT E Ω A O Bw a _ cs d2
    have q2 := hP l P AI hT E Ω A O Bw 1 _ ck d1
    have q3 := hP l P AI hT E Ω A O Bw a _ ct dt
    have hcs : Continuous fun g : ↥(Dec (F := E) A) =>
        ((s.comp (Dec (F := E) A).subtype g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l)) :=
      Units.continuous_val.comp cs
    have hck : Continuous fun g : ↥(Dec (F := E) A) =>
        ((rk1 (μ.comp (Dec (F := E) A).subtype) g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l)) :=
      Units.continuous_val.comp ck
    rw [← e3] at q3
    have key := GlobalTheory.T.fontaineParameter_twist_potentiallySemistable l P AI hT ι E Ω A w h O Bw hj a _ _ hcs hck q1 q2 q3
    rw [e3] at key
    rw [key]
    exact (hW E Ω A w h _ _).2.2.2 g S c (p2 g) (p1 g)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.clAway_holds :
    ClAway := by
  intro E Ω _ _ _ _ _ l _ ι a r w hl S J
  refine ⟨fun h => h.1 hl, fun h => ⟨fun _ => h, ?_⟩⟩
  intro P AI _ A hA O _ _ _ Bw hj
  exact absurd (hj.mem_placesOver hA) hl
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem univ_map_snoc {α : Type*} {t : ℕ} (f : Fin (t + 1) → α) :
    Finset.univ.val.map f =
      Finset.univ.val.map (fun i : Fin t => f i.castSucc) + {f (Fin.last t)} := by
  rw [Fin.univ_castSuccEmb]
  simp [Finset.map_val, Multiset.map_map, add_comm, Function.comp_def]

theorem UpperTheory.Gal.TP.Sub.peelAll_holds :
    PeelOne → ContLeft → ClConj → ClSub → PeelAll := by
  intro hP hC hJ hS E Ω _ _ _ _ _ l _ ι n m' t' r' a' hr' t
  induction t with
  | zero =>
    intro r a hc hss _ _ _
    refine ⟨r, hc, hss, ?_⟩
    intro w S c J m _ h
    simpa using h
  | succ t ih =>
    intro r a hc hss ha hne hid
    obtain ⟨s₁, hs₁, hiso, hid₁⟩ :=
      hP (G E Ω) (Qbar l) (n + t) m' t t' r r' a a' hss hr' hne hid
    have hC' := hC (G E Ω) (Qbar l) (n + t) 1
    have hC1 := hC (G E Ω) (Qbar l) (n + t + 1) 1
    have hcl : Continuous (sumRep s₁ (rk1 (a (Fin.last t)))) := hC1.2.1 _ _ hiso hc
    have hcs₁ : Continuous s₁ := hC'.1 _ _ hcl
    obtain ⟨s, hsc, hss', hcl'⟩ := ih s₁ (fun i => a i.castSucc) hcs₁ hs₁
      (fun i => ha _) (fun i j => hne _ _) hid₁
    refine ⟨s, hsc, hss', ?_⟩
    intro w S c J m hcl0 h
    have h2 := hJ E Ω l ι _ r _ hc hiso w _ _ h
    refine hcl' w S (fun i => c i.castSucc) J (fun i => m i.castSucc) (fun i => hcl0 _) ?_
    refine hS E Ω l ι _ s₁ (a (Fin.last t)) hcs₁ (ha _) w _ (c (Fin.last t)) _
      (m (Fin.last t)) (hcl0 _) ?_
    have e1 : S + Finset.univ.val.map c =
        S + Finset.univ.val.map (fun i : Fin t => c i.castSucc) + {c (Fin.last t)} := by
      rw [univ_map_snoc c, add_assoc]
    have e2 : (fun τ => J τ + Finset.univ.val.map fun i => m i τ) =
        fun τ => J τ + Finset.univ.val.map (fun i : Fin t => m i.castSucc τ) +
          {m (Fin.last t) τ} := by
      funext τ
      rw [univ_map_snoc (fun i => m i τ), add_assoc]
    rw [e1, e2] at h2
    exact h2
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

theorem charFrob_holds : CharFrob := by
  intro E Ω _ _ _ _ _ l _ ι art ha χ n μ h w hw hu A hA
  have hv : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∨ n = 0 := Or.inl hw
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : μ s = 1 := (h.unr_iff ha hv hA).mpr hu s hs
    simp [rk1, h1]
  · have h1 : ((μ σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.val w : ℂˣ) : ℂ))⁻¹ := h.frob_unr ha hv hu hA hσ
    simp [rk1, Matrix.charpoly, Matrix.det_fin_one, h1, Polynomial.map_sub]

end UpperTheory.Gal.TP.Sub

end
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charAbove_holds :
    GlobalTheory.Published.HeckeLAdicCharacter → GlobalTheory.Published.HeckeLAdicCharacterDeRham → GlobalTheory.Published.AlgebraicCharacterWD → PstOfDR → ContLeft → CharAbove := by
  intro H hD hW hP hC E Ω _ _ _ _ _ l _ ι art ha χ n μ h1 h2 h3 w hu P AI hT A h O _ _ _ Bw hj
  obtain ⟨a, ha'⟩ := GlobalTheory.localArtinExists_holds E Ω A w h
  have hξ := GlobalTheory.Published.ParamAboveModel.isComp_loc (w := w) χ
  have d := hD E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj
  have hc : Continuous ((rk1 μ).comp (Dec (F := E) A).subtype) :=
    ((hC (G E Ω) (Qbar l) 0 0).2.2.2 μ h2).comp continuous_subtype_val
  have hr := hP l P AI hT E Ω A O Bw 1 _ hc d.1
  have e := hW E Ω l P AI hT ι art ha χ n μ h1 h2 h3 w A h O Bw hj _ hξ a ha'
  have hun := (GlobalTheory.Published.CharCrysModel.isUnram_iff χ w).2 hu
  refine ⟨?_, d.1, d.2, fun g => ?_⟩
  · rw [← GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ hr, e, GlobalTheory.LocLanglands.Test.unr_lpOfChar_iff ha' hξ.1]
    exact hun
  · have hv : (χ.loc w (a g) : ℂ) = ((χ.val w : ℂˣ) : ℂ) ^ (-deg g) := by
      have ho : GlobalTheory.SmGL.ord (w.adicCompletion E) (atFin w (unif w)) = 1 := by
        rw [GlobalTheory.SmGL.SphCompletion.ord_completion, show Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _ from unif_spec w]
        simp
      have h1 : ∀ x : (w.adicCompletion E)ˣ, χ.loc w x = χ.val w ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x := fun x => by
        have h0 : GlobalTheory.SmGL.ord (w.adicCompletion E) (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) = 0 := by
          have hz : ∀ (y : (w.adicCompletion E)ˣ), GlobalTheory.SmGL.unrChar (w.adicCompletion E) (Units.mk0 2 two_ne_zero) y =
              (Units.mk0 (2:ℂ) two_ne_zero) ^ GlobalTheory.SmGL.ord _ y := fun _ => rfl
          let φ : (w.adicCompletion E)ˣ →* Multiplicative ℤ := MonoidHom.mk' (fun y => Multiplicative.ofAdd (GlobalTheory.SmGL.ord _ y))
            fun y z => by rw [GlobalTheory.SmGL.ord_mul, ofAdd_add]
          have : φ (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion E) x)⁻¹) = 1 := by
            rw [map_mul, map_inv, map_zpow]
            simp [φ, ho, ← ofAdd_zsmul]
          exact this
        have := hun _ ((GlobalTheory.SmGL.ord_eq_zero_iff).1 h0)
        rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at this
        exact this
      rw [h1, ha'.ord_eq, Units.val_zpow_eq_zpow_val]
    rw [e, WD.charPol_eq_prod, GlobalTheory.LocLanglands.eig_lpOfChar]
    simp [unrPol, hv]
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charInj_holds :
    CharInj := by
  intro E Ω _ _ _ _ _ l _ ι art _ χ χ' n n' μ hχ hχ'
  apply GlobalTheory.T.hecke_character_eq_of_cofinite E χ χ'
  have hl : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
  have hfin := Ideal.finite_factors hl
  have h1 := (GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ).1
  have h2 := (GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ').1
  have hev := ((h1.union h2).union hfin).compl_mem_cofinite
  filter_upwards [hev] with v hv
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hv
  obtain ⟨⟨hu, hu'⟩, hd⟩ := hv
  have hl' : (l : 𝓞 E) ∉ v.asIdeal := fun h => hd (Ideal.dvd_span_singleton.mpr h)
  refine ⟨hu, hu', ?_⟩
  obtain ⟨σ, hσ⟩ := toAb_surjective (E := E) (Ω := Ω) (art (localIdele E v (atFin v (unif v))))
  have a := hχ.loc_away (Or.inl hl') (atFin v (unif v)) σ hσ.symm
  have b := hχ'.loc_away (Or.inl hl') (atFin v (unif v)) σ hσ.symm
  rw [← HChar.val_eq χ hu _ (unif_spec v), ← HChar.val_eq χ' hu' _ (unif_spec v)]
  exact Units.ext (ι.symm.injective (a.symm.trans b))
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charEx_holds :
    GlobalTheory.Published.HeckeLAdicCharacter → CharFrob → CharAbove → CharInj → CharEx := by
  classical
  intro H hF hA hI E Ω _ _ _ _ _ l _ ι
  obtain ⟨art, hart, hex⟩ := H E Ω
  have hL : ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
      ∃ r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r :=
    fun χ n h => (hex l ι χ n h).exists
  let L : HChar E → ((E →+* ℂ) → ℤ) → (G E Ω →* (Qbar l)ˣ) :=
    fun χ n => if h : IsAlgPos χ n then (hL χ n h).choose else 1
  have hspec : ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
      Continuous (L χ n) ∧ IsLAdicOf art ι χ n (L χ n) := by
    intro χ n h
    have e : L χ n = (hL χ n h).choose := dif_pos h
    rw [e]
    exact (hL χ n h).choose_spec
  refine ⟨L, fun χ n h => ⟨(hspec χ n h).1, fun w hw => ⟨fun hl => ?_, ?_⟩⟩, fun χ n χ' n' h h' e => ?_⟩
  · exact hF E Ω l ι art hart χ n (L χ n) (hspec χ n h).2 w hl hw
  · exact hA E Ω l ι art hart χ n (L χ n) h (hspec χ n h).1 (hspec χ n h).2 w hw
  · exact hI E Ω l ι art hart χ χ' n n' (L χ n) (hspec χ n h).2 (e ▸ (hspec χ' n' h').2)
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub
open GlobalTheory.PRep Formalism.UG GlobalTheory.BCT

theorem UpperTheory.Gal.TP.Sub.satAE_holds :
    SatAE := by
  intro E _ _ _ a U hU
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU E a) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hLo : IsOpen (L : Set (finU E a)) := (hU.aut φ hφ).level
  filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E a L hLo] with w hw hs
  obtain ⟨hJo, hJc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨σ, hσ, v, hv0, hv⟩ := GlobalTheory.T.exists_localComponent_eigenvector_splitPlace E a U hU w hs (GlobalTheory.LFun.KGL w a) hJo hJc 1 φ hφ hφ0
    (fun x hx hxK => by
      have h : RU E a x φ = φ := hw x hx hxK hx.1
      simpa using h)
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w a) :=
    (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by simpa using hv ⟨k, hk⟩, hv0⟩
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred hsph
  exact ⟨B, σ, hσ, hB⟩
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.frobId_holds :
    DenseId → CpFacts → FrobId := by
  intro hDI hCp E Ω _ _ _ _ _ _ l _ ι d t r r' a a' hr hr' ha ha' hev
  have hS := Filter.eventually_cofinite.1 hev
  refine hDI (G E Ω) l d d t t r r' a a' hr hr' ha ha' _
    (GlobalTheory.SplitAttUniq.dense_splitFrobInv_away E Ω l (Fact.out) _ hS) ?_
  rintro g ⟨w, hw, hsp, hl, A, hA, hF⟩
  obtain ⟨S₀, c, c', h1, h2, h3, h4⟩ := (not_not.1 hw) hsp
  have lin_map : ∀ (b : Fin t → G E Ω →* (Qbar l)ˣ) (e : Fin t → ℂ),
      (∀ i, FrobEig ι (rk1 (b i)) w {e i}) →
      (lin b g).map ι.toRingHom = ∏ i, (X - C (e i)) := by
    intro b e hb
    rw [lin, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h := ((hb i) A hA).2 g⁻¹ hF
    rw [inv_inv] at h
    have h' : cp (rk1 (b i)) g = X - C (b i g : Qbar l) := (hCp (G E Ω) (Qbar l) 0 0).2.1 (b i) g
    rw [← h']
    simpa using h
  have cp_map : ∀ (s : G E Ω →* GL (Fin d) (Qbar l)) (e : Fin t → ℂ),
      FrobEig ι s w (S₀ + Finset.univ.val.map e) →
      (cp s g).map ι.toRingHom = (S₀.map fun z => X - C z).prod * ∏ i, (X - C (e i)) := by
    intro s e hs
    have h := (hs A hA).2 g⁻¹ hF
    rw [inv_inv] at h
    rw [cp, h, Multiset.map_add, Multiset.prod_add, Multiset.map_map]
    rfl
  apply Polynomial.map_injective ι.toRingHom ι.injective
  rw [Polynomial.map_mul, Polynomial.map_mul, cp_map r c h1, cp_map r' c' h2, lin_map a' c' h4,
    lin_map a c h3]
  ring
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub
end

section
namespace UpperTheory.Gal.TP.Sub

theorem pstOfDR : PstOfDR := pstOfDR_holds GlobalTheory.deRham_potentiallySemistable

theorem frobSub : FrobSub := frobSub_holds cpFacts_holds

theorem clConj : ClConj := clConj_holds cpFacts_holds contLeft_holds pstOfDR

theorem clSub : ClSub := clSub_holds frobSub sumDR_holds pstOfDR wDFacts_holds

theorem clTw : ClTw := clTw_holds frobSub twLoc_holds twJumps_holds pstOfDR wDFacts_holds contLeft_holds

theorem peelAll : PeelAll :=
  peelAll_holds (peelOne_holds dgFacts_holds cpFacts_holds eigTransfer_holds eigSum_holds splitLine_holds sSLeft_holds)
    contLeft_holds clConj clSub

theorem charEx : CharEx :=
  charEx_holds PositivityTheory.Stage1.PM.heckeLAdicCharacter charFrob_holds
    (charAbove_holds PositivityTheory.Stage1.PM.heckeLAdicCharacter HodgeLocalDeRhamField.HLdR.field_outright
      (UpperTheory.Lit.CharWD.algebraicCharacterWD GlobalTheory.globalArtinReciprocity_holds HodgeLocalDeRhamField.HLdR.field_outright GlobalTheory.deRham_potentiallySemistable) pstOfDR
      contLeft_holds) charInj_holds


theorem atPlace : AtPlace :=
  atPlace_holds charEx satAE_holds (frobId_holds (denseId_holds cpFacts_holds dgFacts_holds) cpFacts_holds) peelAll clTw
    clAway_holds contLeft_holds sSLeft_holds


end UpperTheory.Gal.TP.Sub
end
