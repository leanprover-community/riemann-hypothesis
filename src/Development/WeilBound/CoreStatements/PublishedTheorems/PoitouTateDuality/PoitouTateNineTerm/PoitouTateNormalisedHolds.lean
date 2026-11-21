import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsNineAdd
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsDataEx
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeZeroMiddle
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeOneMiddle
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeTwoMiddle
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeZeroLeft
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeOneLeft
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.DegreeTwoCohomologyComparisonLeft
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualQZ
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PfContActionTwDualC
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr0B
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr1C
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr2
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.NineAddOfFound2Fun
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNormalisedOfNine

section
noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxHeartbeats 1000000 in
theorem nineAdd_of_found3 {N : ℕ} [NeZero N]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {α : Type} (S : Finset α) [Fintype ↥(↑S : Set α)] {Hv : ↥(↑S : Set α) → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
    [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
    (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    [Finite M] (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ)
    (δ₁ : (cohomology (dualRep D M) 2 →+ QZ) →+ cohomology M 1)
    (δ₂ : (cohomology (dualRep D M) 1 →+ QZ) →+ cohomology M 2)
    (hx : Function.Injective (ptGlobalToLocal φ M 0).hom ∧
      Function.Exact (ptGlobalToLocal φ M 0).hom (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) ∧
      Function.Exact (ptLocalDualMap φ D M inv (show 0 + 2 = 2 from rfl)) δ₁ ∧
      Function.Exact δ₁ (ptGlobalToLocal φ M 1).hom ∧
      Function.Exact (ptGlobalToLocal φ M 1).hom (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) ∧
      Function.Exact (ptLocalDualMap φ D M inv (show 1 + 1 = 2 from rfl)) δ₂ ∧
      Function.Exact δ₂ (ptGlobalToLocal φ M 2).hom ∧
      Function.Exact (ptGlobalToLocal φ M 2).hom (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)) ∧
      Function.Surjective (ptLocalDualMap φ D M inv (show 2 + 0 = 2 from rfl)))

    {H0 H1 H2 : Type} [AddCommGroup H0] [Module (ZMod N) H0] [AddCommGroup H1] [Module (ZMod N) H1]
    [AddCommGroup H2] [Module (ZMod N) H2]
    {L0 L1 L2 : S → Type} [∀ k, AddCommGroup (L0 k)] [∀ k, Module (ZMod N) (L0 k)]
    [∀ k, AddCommGroup (L1 k)] [∀ k, Module (ZMod N) (L1 k)]
    [∀ k, AddCommGroup (L2 k)] [∀ k, Module (ZMod N) (L2 k)]
    {Y0 Y1 Y2 : Type} [AddCommGroup Y0] [Module (ZMod N) Y0] [AddCommGroup Y1] [Module (ZMod N) Y1]
    [AddCommGroup Y2] [Module (ZMod N) Y2]
    {W0 W1 W2 : S → Type} [∀ k, AddCommGroup (W0 k)] [∀ k, Module (ZMod N) (W0 k)]
    [∀ k, AddCommGroup (W1 k)] [∀ k, Module (ZMod N) (W1 k)]
    [∀ k, AddCommGroup (W2 k)] [∀ k, Module (ZMod N) (W2 k)]
    (res0 : ∀ k, H0 →ₗ[ZMod N] L0 k) (res1 : ∀ k, H1 →ₗ[ZMod N] L1 k)
    (res2 : ∀ k, H2 →ₗ[ZMod N] L2 k)
    (rs0 : ∀ k, Y0 →ₗ[ZMod N] W0 k) (rs1 : ∀ k, Y1 →ₗ[ZMod N] W1 k) (rs2 : ∀ k, Y2 →ₗ[ZMod N] W2 k)
    (P0 : ∀ k, L0 k → W2 k → ZMod N) (P1 : ∀ k, L1 k → W1 k → ZMod N)
    (P2 : ∀ k, L2 k → W0 k → ZMod N)
    (f0 : H0 →ₗ[ZMod N] ∀ k, L0 k) (f1 : (∀ k, L0 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y2)
    (f3 : H1 →ₗ[ZMod N] ∀ k, L1 k) (f4 : (∀ k, L1 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y1)
    (f6 : H2 →ₗ[ZMod N] ∀ k, L2 k) (f7 : (∀ k, L2 k) →ₗ[ZMod N] Module.Dual (ZMod N) Y0)
    (hf0 : ∀ x k, f0 x k = res0 k x) (hf3 : ∀ x k, f3 x k = res1 k x)
    (hf6 : ∀ x k, f6 x k = res2 k x)
    (hf1 : ∀ x y, f1 x y = ∑ k, P0 k (x k) (rs2 k y))
    (hf4 : ∀ x y, f4 x y = ∑ k, P1 k (x k) (rs1 k y))
    (hf7 : ∀ x y, f7 x y = ∑ k, P2 k (x k) (rs0 k y))
    {BM0 : (H0 ≃+ cohomology M 0) → Prop}
    {CM0 : (∀ k : S, L0 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 0) → Prop}
    (hM0 : ∃ (E : H0 ≃+ cohomology M 0) (Ev : ∀ k : S, L0 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 0),
      (∀ k x, Ev k (res0 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) M k 0 (E x)) ∧ BM0 E ∧ CM0 Ev)
    {TranslateJetMomentLawAnyIdempotentLevel : (H1 ≃+ cohomology M 1) → Prop}
    {JInvariantIntegrality : (∀ k : S, L1 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 1) → Prop}
    (hM1 : ∃ (E : H1 ≃+ cohomology M 1) (Ev : ∀ k : S, L1 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 1),
      (∀ k x, Ev k (res1 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) M k 1 (E x)) ∧ TranslateJetMomentLawAnyIdempotentLevel E ∧ JInvariantIntegrality Ev)
    {LocallyConstantJetMomentLawAnyIdempotentLevel : (H2 ≃+ cohomology M 2) → Prop}
    {CM2 : (∀ k : S, L2 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 2) → Prop}
    (hM2 : ∃ (E : H2 ≃+ cohomology M 2) (Ev : ∀ k : S, L2 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom M) 2),
      (∀ k x, Ev k (res2 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) M k 2 (E x)) ∧ LocallyConstantJetMomentLawAnyIdempotentLevel E ∧ CM2 Ev)
    {BD0 : (Y0 ≃+ cohomology (dualRep D M) 0) → Prop}
    {weightDegreeConstant : (∀ k : S, W0 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 0) → Prop}
    (hD0 : ∃ (E : Y0 ≃+ cohomology (dualRep D M) 0) (Ev : ∀ k : S, W0 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 0),
      (∀ k x, Ev k (rs0 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) (dualRep D M) k 0 (E x)) ∧ BD0 E ∧ weightDegreeConstant Ev)
    {BD1 : (Y1 ≃+ cohomology (dualRep D M) 1) → Prop}
    {CD1 : (∀ k : S, W1 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 1) → Prop}
    (hD1 : ∃ (E : Y1 ≃+ cohomology (dualRep D M) 1) (Ev : ∀ k : S, W1 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 1),
      (∀ k x, Ev k (rs1 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) (dualRep D M) k 1 (E x)) ∧ BD1 E ∧ CD1 Ev)
    {BD2 : (Y2 ≃+ cohomology (dualRep D M) 2) → Prop}
    {CD2 : (∀ k : S, W2 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 2) → Prop}
    (hD2 : ∃ (E : Y2 ≃+ cohomology (dualRep D M) 2) (Ev : ∀ k : S, W2 k ≃+ cohomology (Rep.res (φ ⟨k.1, Finset.mem_coe.2 k.2⟩).toMonoidHom (dualRep D M)) 2),
      (∀ k x, Ev k (rs2 k x) = ptRes (fun v : S => φ ⟨v.1, Finset.mem_coe.2 v.2⟩) (dualRep D M) k 2 (E x)) ∧ BD2 E ∧ CD2 Ev)
    (hQ0 : ∀ Ev Fv, CM0 Ev → CD2 Fv → ∀ (k : S) a b, zmodToQZ N (P0 k a b) =
      - inv ⟨k.1, Finset.mem_coe.2 k.2⟩ (cupPairing (ptLocalEval φ D M ⟨k.1, Finset.mem_coe.2 k.2⟩) (rfl : 0 + 2 = 2) (Ev k a) (Fv k b)))
    (hQ1 : ∀ Ev Fv, JInvariantIntegrality Ev → CD1 Fv → ∀ (k : S) a b, zmodToQZ N (P1 k a b) =
      inv ⟨k.1, Finset.mem_coe.2 k.2⟩ (cupPairing (ptLocalEval φ D M ⟨k.1, Finset.mem_coe.2 k.2⟩) (rfl : 1 + 1 = 2) (Ev k a) (Fv k b)))
    (hQ2 : ∀ Ev Fv, CM2 Ev → weightDegreeConstant Fv → ∀ (k : S) a b, zmodToQZ N (P2 k a b) =
      - inv ⟨k.1, Finset.mem_coe.2 k.2⟩ (cupPairing (ptLocalEval φ D M ⟨k.1, Finset.mem_coe.2 k.2⟩) (rfl : 2 + 0 = 2) (Ev k a) (Fv k b))) :
    NineAdd f0 f1 f3 f4 f6 f7 := by
  obtain ⟨E0, Ev0, sq0, -, c0⟩ := hM0
  obtain ⟨E1, Ev1, sq1, -, c1⟩ := hM1
  obtain ⟨E2, Ev2, sq2, -, c2⟩ := hM2
  obtain ⟨F0, Fv0, tq0, -, d0⟩ := hD0
  obtain ⟨F1, Fv1, tq1, -, d1⟩ := hD1
  obtain ⟨F2, Fv2, tq2, -, d2⟩ := hD2
  exact nineAdd_of_found2 φ (finsetCoeEquiv S) D M inv δ₁ δ₂ hx res0 res1 res2 rs0 rs1 rs2 P0 P1 P2 f0 f1 f3 f4 f6 f7
    hf0 hf3 hf6 hf1 hf4 hf7 E0 E1 E2 Ev0 Ev1 Ev2 F0 F1 F2 Fv0 Fv1 Fv2 sq0 sq1 sq2 tq0 tq1 tq2
    (hQ0 Ev0 Fv2 c0 d2) (hQ1 Ev1 Fv1 c1 d1) (hQ2 Ev2 Fv0 c2 d0)

end PositivityTheory.Lit1.PTN
end
end

section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxHeartbeats 8000000 in
theorem nineAdd_core (Kf : FiniteSubfield)
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] {l r : ℕ} [Fact l.Prime] (hl : l ≠ 2 ∨ IsTotallyComplex Kf.1) (hr : 0 < r)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : PositivityTheory.PoitouTateConclusion.InvNormalised ζ inv)
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) (d : FoundData Kf S l r ζ Av μ M ρ) :
    NineAdd (loc0 S Av ρ) (tr0 S Av μ (invAt S Av μ hμ inv) ρ) (loc1 S Av ρ)
      (tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ) (loc2 S Av ρ) (tr2 S Av μ (invAt S Av μ hμ inv) ρ) := by
  haveI := d.isDiscrete
  haveI : Finite d.A := Finite.of_equiv M d.eM.toEquiv
  haveI hDd : IsDiscreteRep (dualRep (gsRoots (K := Kf) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) := isDiscreteRep_dualRep _ _
  haveI hDv : ∀ v : S, IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (K := Kf) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) :=
    fun v => isDiscreteRep_res_dualRep_of_finite _ _ _
  have hρ' : ContAction (twDual μ ρ) := contAction_twDual_C S μ hμ ρ hρ
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hSN : ∀ v : HeightOneSpectrum (𝓞 Kf.1), (((l ^ r : ℕ) : ℕ) : 𝓞 Kf.1) ∈ v.asIdeal →
      v ∈ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) := by
    intro v hv
    rw [Nat.cast_pow] at hv
    exact Finset.mem_coe.2 (hS v (v.isPrime.mem_of_pow_mem r hv))
  have hK : Odd (l ^ r) ∨ IsTotallyComplex Kf.1 := by
    rcases hl with h | h
    · exact Or.inl ((Fact.out : l.Prime).odd_of_ne_two h).pow
    · exact Or.inr h
  have hMt : ∀ m : d.A, (l ^ r) • m = 0 := by
    intro m
    rw [← d.eM.apply_symm_apply m, ← map_nsmul, nsmul_eq_zero_of_zmod, map_zero]
  have F9 :=
    poitouTate_nineTerm_gs (K := Kf) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs hSN hK d.A hMt
  have hM0 := tate_duality_degree_zero_middle Kf S ζ Av μ ρ d hρ
  have hM1 := tate_duality_degree_one_middle Kf S ζ Av μ ρ d hρ
  have hM2 := tate_duality_degree_two_middle Kf S ζ Av μ ρ d hρ
  have hD0 := tate_duality_degree_zero_left Kf S ζ Av μ ρ d hρ'
  have hD1 := tate_duality_degree_one_left Kf S ζ Av μ ρ d hρ'
  have hD2 := degree_two_cohomology_comparison_left Kf S ζ Av μ ρ d hρ'
  exact nineAdd_of_found3 (N := l ^ r) S (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A (gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r)) _ _
    F9
    (fun k => resH0 ρ (locFam S Av k)) (fun k => resH1 ρ (locFam S Av k) (continuous_locFam S Av k))
    (fun k => resH2 ρ (locFam S Av k) (continuous_locFam S Av k))
    (fun k => resH0 (twDual μ ρ) (locFam S Av k))
    (fun k => resH1 (twDual μ ρ) (locFam S Av k) (continuous_locFam S Av k))
    (fun k => resH2 (twDual μ ρ) (locFam S Av k) (continuous_locFam S Av k))
    (fun k a b => invAt S Av μ hμ inv k (cupH0H2TwistedDual μ ρ (locFam S Av k) a b))
    (fun k a b => invAt S Av μ hμ inv k (cupH1H1TwistedDual μ ρ (locFam S Av k) (hρ.comp' (continuous_locFam S Av k)) b a))
    (fun k a b => invAt S Av μ hμ inv k (cup20 μ ρ (locFam S Av k) a b))
    (loc0 S Av ρ) (tr0 S Av μ (invAt S Av μ hμ inv) ρ) (loc1 S Av ρ)
    (tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ) (loc2 S Av ρ) (tr2 S Av μ (invAt S Av μ hμ inv) ρ)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x y => poitouTateNineTerm_transgressionZero_apply S Av μ (invAt S Av μ hμ inv) ρ x y)
    (fun x y => poitouTateNineTerm_transgressionOne_apply S Av μ (invAt S Av μ hμ inv) ρ hρ x y)
    (fun x y => poitouTateNineTerm_transgressionTwo_apply S Av μ (invAt S Av μ hμ inv) ρ x y)
    hM0 hM1 hM2 hD0 hD1 hD2
    (fun Ev Fv c c' k a b => locTr0_B Kf S hr ζ hζ inv hinv hS Av hAv μ hμ ρ hρ d k (Ev k) (c k) (Fv k) (c' k) a b)
    (fun Ev Fv c c' k a b => locTr1_C Kf S hr ζ hζ inv hinv hS Av hAv μ hμ ρ hρ d k (Ev k) (c k) (Fv k) (c' k) a b)
    (fun Ev Fv c c' k a b => locTr2' Kf S hr ζ hζ inv hinv hS Av hAv μ hμ ρ hρ d k (Ev k) (c k) (Fv k) (c' k) a b)

end PositivityTheory.Lit1.PTN
end
end

section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem nineAddFS_V : NineAddFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  exact (foundData_nonempty ⟨K, inferInstance⟩ S hr ζ hζ hS Av hAv μ hμ ρ hρ).elim fun d =>
    nineAdd_core ⟨K, inferInstance⟩ hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ d

theorem poitouTateNormalised_holds : GlobalTheory.Published.PoitouTateNormalised :=
  PositivityTheory.PTN.poitouTateNormalised_of_nine (nineCmpFS_of_nineAddFS nineAddFS_V)

end PositivityTheory.Lit1.PTN
end
end
