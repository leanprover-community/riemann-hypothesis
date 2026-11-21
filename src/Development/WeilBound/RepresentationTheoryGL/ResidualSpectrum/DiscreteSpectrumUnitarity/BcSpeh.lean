import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.DiscreteSpectrumUnitarity.ExhaustionRegularFiniteClause
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteLeOfClosureClasses

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.Re

section Pair

theorem iso (H : UsedReg) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]
    {N a d : ℕ} (hN : 1 ≤ N) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {π π' : CuspSub E a} (h : IsNormalised π)
    (h' : IsNormalised π') (e : IsSpehOf V π d) (e' : IsSpehOf V π' d) : π.Iso π' :=
  Quotient.exact (eq_of_heq (Sigma.mk.inj ((H E N hN).2.2.1 V hV a d a d π π' h h' e e').2).2)

theorem isCsd_of_isSpehOf (H : UsedReg) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {N a d : ℕ} (hN : 1 ≤ N) {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V)
    (hc : IsCsdGL V) {π : CuspSub E a} (hπ : IsNormalised π) (h : IsSpehOf V π d) : π.IsCsd :=
  GlobalTheory.ThetaPull.isCsd_of_iso (iso H hN hV (GlobalTheory.ThetaPull.isNormalised_thetaSub hπ) hπ
    (GlobalTheory.ThetaPull.isSpehOf_thetaSub hV.stable hc h) h)

end Pair

section Local

open GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.BcSpehProof

theorem isUnitarisable_of_isLocComp (H : UsedReg) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {a : ℕ} (ha : 1 ≤ a) (P : CuspSub E a) (hP : GlobalTheory.DiscSpec.IsNormalised P)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : LocIrr w a) (hρ : P.IsLocComp w ρ) : IsUnitarisable ρ.ρ := by
  obtain ⟨V, hV, hS⟩ := (H E a ha).2.1 a P rfl hP
  have hc := (H E a ha).2.2.2 V hV a 1 P hP hS
  obtain ⟨-, σ', -, hσ'⟩ := hc.exLoc w
  obtain ⟨hd, h1⟩ := hc.loc w ρ σ' hρ hσ'
  obtain ⟨hd', h2⟩ := GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of ρ.ρ ρ.smooth ρ.irred)
  obtain ⟨e⟩ := h1.unique h2
  have hu := GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E a V hV w σ' hσ'
  exact isUnitarisable_of_equiv' ((GlobalTheory.LocGL.IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e).symm hu

end Local

end PositivityTheory.Rg.Rs.Re

end
end

section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.BcSpehProof

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.Re

theorem baseChange_speh_of_discreteSeries (H : UsedReg)
    (hW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
      ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ τ : E →+* ℂ, ∃ lam : Formalism.BasicNotions.DomWeight n, HasWeightAt π τ lam)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 1 ≤ n)
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {c : ℕ} {N : Fin c → ℕ} {h : ∑ i, N i = n}
    {V : ∀ i, Submodule ℂ (Sm E (N i))} {σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))}
    {m : Fin c → (E →+* ℂ) → Multiset ℂ} (bc : IsBaseChange π h V σ m) (a d : Fin c → ℕ) (P : ∀ i, CuspSub E (a i))
    (hPn : ∀ i, GlobalTheory.DiscSpec.IsNormalised (P i)) (hPs : ∀ i, GlobalTheory.DiscSpec.IsSpehOf (V i) (P i) (d i))
    (hNad : ∀ i, N i = d i * a i) :
    ∃ (c : ℕ) (a d : Fin c → ℕ) (h : ∑ i, d i * a i = n) (P : ∀ i, CuspSub E (a i)) (ρ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (a i))
        (m : Fin c → (E →+* ℂ) → Multiset ℂ) (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), LocIrr w (d i * a i)), Parts π a d h P ρ m ∧
        (∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ ∧ GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ) ∧
        ∀ w, IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd h w (σ · w)) := by
  have hN : ∀ i, 1 ≤ N i := bc.pos
  have hc : ∀ i, GlobalTheory.DiscSpec.HasSpehComp (V i) (P i) (d i) := fun i =>
    (H E (N i) (hN i)).2.2.2 (V i) (bc.discrete i) (a i) (d i) (P i) (hPn i) (hPs i)
  choose ρ σ' hρ hσ' using fun i w => (hc i).exLoc w
  choose m' hm1 hm2 using fun i τ => (hc i).inf τ
  have hmm : ∀ i τ, m i τ = GlobalTheory.DefiniteBC.spehInf (d i) (m' i τ) := fun i τ =>
    (hasInfCharGL_unique (bc.discrete i).ne_bot (bc.inf i τ) (hm2 i τ)).trans (spehInf_eq _ _)
  have hpos : ∀ i, 1 ≤ a i ∧ 1 ≤ d i := fun i => by
    have := hN i
    rw [hNad i] at this
    exact ⟨Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this, Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at this⟩
  have hcsd : ∀ i, (P i).IsCsd := fun i =>
    isCsd_of_isSpehOf H (hN i) (bc.discrete i) (bc.csd i) (hPn i) (hPs i)
  have hsp : ∀ i w, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ :=
    fun i w => (hc i).loc w (ρ i w) (σ i w) (hρ i w) (bc.loc i w)
  have hun : ∀ i w, IsUnitarisable (ρ i w).ρ ∧ IsUnitarisable (σ i w).ρ := fun i w =>
    ⟨isUnitarisable_of_isLocComp H (hpos i).1 (P i) (hPn i) w (ρ i w) (hρ i w),
      GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable E (N i) (V i) (bc.discrete i) w (σ i w) (bc.loc i w)⟩
  have hm0 : ∀ i τ, m i τ ≠ 0 := fun i τ h0 => by
    have h1 := (bc.inf i τ).1
    rw [h0, Multiset.card_zero] at h1
    have := hN i
    omega
  obtain rfl : N = fun i => d i * a i := funext hNad
  refine ⟨c, a, d, h, P, ρ, m', σ, ⟨hpos, hcsd, hρ, hm1, fun τ lam hl => ?_, fun i j hd hs => ?_, ?_⟩,
    fun i w => ⟨(hun i w).1, (hun i w).2, hsp i w⟩, bc.split⟩
  · rw [← bc.weight τ lam hl]
    exact Finset.sum_congr rfl fun i _ => (hmm i τ).symm
  · obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨lam, hl⟩ := hW E n hn π hπ τ
    refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (hm0 i τ) ?_
    rw [hmm i τ, hmm j τ, hd, hasInfChar_eq_of_sigma hs (hm1 i τ) (hm1 j τ)]
  · intro w s ϖ q hs hU α hα
    exact GlobalTheory.T.satakeParameter_spherical_product_spehQuotients E w c n a d h (ρ · w) (σ · w) (fun i => (hpos i).2) (fun i => hsp i w) _
      (bc.inert w s ϖ q hs hU α hα)

theorem regInt_part {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 1 ≤ n)
    {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {c : ℕ} {N : Fin c → ℕ} {h : ∑ i, N i = n}
    {V : ∀ i, Submodule ℂ (Sm E (N i))} {σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))}
    {m : Fin c → (E →+* ℂ) → Multiset ℂ} (bc : IsBaseChange π h V σ m) (i : Fin c) (τ : E →+* ℂ) :
    RegInt (V i) τ := by
  obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn π hπ τ
  have hle : m i τ ≤ ∑ j, m j τ :=
    Finset.single_le_sum (f := fun j => m j τ) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
  rw [bc.weight τ lam hl] at hle
  exact regInt_of_le (bc.inf i τ) hle (nodup_infOfWeight lam) (infOfWeight_int lam)

end PositivityTheory.Rg.Rs.Re

section Cm

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh GlobalTheory.DiscreteSpectrumCM

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.Re

end PositivityTheory.Rg.Rs.Re

end Cm

end
end
