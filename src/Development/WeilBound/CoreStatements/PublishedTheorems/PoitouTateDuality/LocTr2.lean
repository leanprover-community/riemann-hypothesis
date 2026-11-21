import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsData
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalInv
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsCup
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TransferCupDegreeZeroTwo

section
noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem transfer_cup_degree_two_zero {Lv Hv : Type} [Group Lv] [TopologicalSpace Lv] [IsTopologicalGroup Lv]
    [Group Hv] [TopologicalSpace Hv] [IsTopologicalGroup Hv] (ev : Hv ≃* Lv)
    (hevc : Continuous ev.toMonoidHom) {R : Type} [CommRing R] {M M' P : Type}
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [DiscreteTopology M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [DiscreteTopology P]
    (rho : Representation R Lv M) (rho' : Representation R Lv M') (rhoP : Representation R Lv P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (A B C : Rep.{0} (ULift.{0} ℤ) Hv) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V)
    (heA : ∀ σ m, eA (rho (ev σ) m) = A.ρ σ (eA m))
    (heB : ∀ σ m, eB (rho' (ev σ) m) = B.ρ σ (eB m))
    (μ : A ⊗ B ⟶ C) (rel : P → C.V → Prop)
    (hbμ : ∀ x y, rel (b x y) (μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y)))
    (E : H2 rho ≃+ cohomology A 2)
    (hE : ∀ (z : ↥(Z2 rho)) (x : cocycles A 2),
      (∀ s, cochainOf A (cocycleι A 2 x) s = eA (z.1 (ev (s 0), ev (s 1)))) →
        E (Submodule.Quotient.mk z) = cohomologyπ A 2 x)
    (E' : ↥(H0 rho') ≃+ cohomology B 0)
    (hE' : ∀ (z : ↥(H0 rho')) (x : cocycles B 0),
      (∀ s, cochainOf B (cocycleι B 0 x) s = eB z.1) → E' z = cohomologyπ B 0 x)
    {Q : Type} [AddCommGroup Q] (jp : H2 rhoP →+ Q) (J : cohomology C 2 →+ Q)
    (hJ : ∀ (W : ↥(Z2 rhoP)) (x : cocycles C 2),
      (∀ s, rel (W.1 (ev (s 0), ev (s 1))) (cochainOf C (cocycleι C 2 x) s)) →
        jp (Submodule.Quotient.mk W) = - J (cohomologyπ C 2 x))
    (z : ↥(Z2 rho)) (m : ↥(H0 rho')) :
    jp (cupProductH2H0 rho rho' rhoP b hb hbe (Submodule.Quotient.mk z) m) =
      - J (cupPairing μ (rfl : 2 + 0 = 2) (E (Submodule.Quotient.mk z)) (E' m)) := by
  obtain ⟨e2, he2a, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 Hv R M (rho.comp ev.toMonoidHom) A eA heA
  obtain ⟨x2, hx2⟩ := he2a (restrictCocycles2 rho ev.toMonoidHom hevc z)
  have hm : ∀ σ, (rho'.comp ev.toMonoidHom) σ m.1 = m.1 := fun σ => (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2 (ev σ)
  obtain ⟨x0, hx0⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.exists_coc B 0 (fun _ => eB m.1) (IsLocallyConstant.const _)
    (by
      refine (PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp (rho'.comp ev.toMonoidHom) B eB heB 0 fun _ => m.1).trans ?_
      funext s
      rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_zero, hm (s 0), sub_self]
      exact map_zero eB)
  have hmB : ∀ σ, B.ρ σ (eB m.1) = eB m.1 := fun σ => by
    rw [← heB]
    exact congrArg eB (hm σ)
  have hEz : E (Submodule.Quotient.mk z) = cohomologyπ A 2 x2 := hE z x2 (fun s => hx2 s)
  have hEm : E' m = cohomologyπ B 0 x0 := hE' m x0 (fun s => congrFun hx0 s)
  rw [hEz, hEm, cupPairing_cohomologyπ]
  refine hJ (cupCocycleZ2H0 rho rho' rhoP b hb hbe z m) _ (fun s => ?_)
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles]
  rw [show (cochainOf _ (cocycleι _ 0 x0) fun j : Fin 0 => s ⟨2 + j, by omega⟩) = eB m.1 from
    congrFun hx0 _]
  rw [hmB]
  rw [show (cochainOf _ (cocycleι _ 2 x2) fun i : Fin 2 => s ⟨i, by omega⟩) =
    eA (z.1 (ev (s 0), ev (s 1))) from by rw [hx2]; rfl]
  exact hbμ _ _

end PositivityTheory.Lit1.PTN
end
end

section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh
  GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

set_option maxHeartbeats 2000000 in

theorem locTr2' (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (hr : 0 < r) (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : PositivityTheory.PoitouTateConclusion.InvNormalised ζ inv)
    (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] [Finite d.A] (v : S)
    [IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))]
    (E : H2 (ρ.comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 2)
    (hE : ∀ (z : ↥(Z2 (ρ.comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 2),
      (∀ s, cochainOf _ (cocycleι _ 2 x) s = d.eM (z.1 (d.ev v (s 0), d.ev v (s 1)))) → E (Submodule.Quotient.mk z) = cohomologyπ _ 2 x)
    (E' : ↥(H0 ((twDual μ ρ).comp (locFam S Av v))) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 0)
    (hE' : ∀ (z : ↥(H0 ((twDual μ ρ).comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 0),
      (∀ s, cochainOf _ (cocycleι _ 0 x) s = d.eD z.1) → E' z = cohomologyπ _ 0 x)
    (a : H2 (ρ.comp (locFam S Av v))) (b : ↥(H0 ((twDual μ ρ).comp (locFam S Av v)))) :
    zmodToQZ (l ^ r) (invAt S Av μ hμ inv v (cup20 μ ρ (locFam S Av v) a b)) =
      - gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cupPairing (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩) (rfl : 2 + 0 = 2) (E a) (E' b)) := by
  classical
  induction a using Submodule.Quotient.induction_on with
  | H z => ?_
  have hc1 : Continuous (d.ev v).toMonoidHom := (d.hev_cont v).1
  have heA := hloc2 ρ (locFam S Av v) (d.ev v) (fun g => d.e g) d.A d.eM d.hM (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (d.hev v)
  have heB := hloc2 (twDual μ ρ) (locFam S Av v) (d.ev v) (fun g => d.e g)
    (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) d.eD d.hD (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (d.hev v)
  have hbμ : ∀ (x : M) (y : TDual (ZMod (l ^ r)) M),
      ((((Additive.toMul ((ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩).hom
          (d.eM x ⊗ₜ[ULift.{0} ℤ] d.eD y)) :
        rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
        (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
        ζ ^ (evalPair x y).val := fun x y => d.hDζ y x
  have hJ : ∀ (W : ↥(Z2 ((charRep μ).comp (locFam S Av v))))
      (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r))) 2),
      (∀ s, ((((Additive.toMul (cochainOf _ (cocycleι _ 2 x) s) :
          rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
          (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
          maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) =
          ζ ^ (W.1 (d.ev v (s 0), d.ev v (s 1))).val) →
      ((zmodToQZ (l ^ r)).comp (invAt S Av μ hμ inv v).toAddMonoidHom) (Submodule.Quotient.mk W) =
        - gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r) ⟨v.1, Finset.mem_coe.2 v.2⟩ (cohomologyπ _ 2 x) := fun W x h =>
    @invCmp Kf ‹_› ‹_› (S : Set (HeightOneSpectrum (𝓞 Kf.1))) inferInstance l r ‹_› hr (fun w hw => Finset.mem_coe.2 (hS w hw)) ζ hζ
      inv hinv d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ (Av v) (hAv v) (d.ev v) (d.hιs v) (d.hev_cont v).1
      (cocycles2Map ((charRep μ).comp (locFam S Av v)) (muLoc Kf.1 l r (Av v)) LinearMap.id continuous_id
        (locFam_apply_eq S Av μ hμ v) W) x h
  exact transfer_cup_degree_two_zero (d.ev v) hc1 (ρ.comp (locFam S Av v)) ((twDual μ ρ).comp (locFam S Av v))
    ((charRep μ).comp (locFam S Av v)) evalPair continuous_of_discreteTopology
    (fun g x y => evalPair_equiv μ ρ (locFam S Av v g) x y)
    (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))
    (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r))) d.eM d.eD heA heB
    (ptLocalEval (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A ⟨v.1, Finset.mem_coe.2 v.2⟩)
    (fun c y => ((((Additive.toMul y :
        rootsOfUnity (l ^ r) (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))) :
        (maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))))ˣ) :
        maxUnramifiedOutside Kf.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) : AlgebraicClosure ℚ) = ζ ^ c.val)
    hbμ E hE E' hE' _ _ hJ z b

end PositivityTheory.Lit1.PTN
end
end
