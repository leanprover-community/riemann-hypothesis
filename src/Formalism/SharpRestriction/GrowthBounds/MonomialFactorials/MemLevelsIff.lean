import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankEqSpanGen

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Dim

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem xi_span (ι : ℚ_[p] →+* KK O) {N r t b : ℕ} (g : MvPolynomial (BVar N r t) (KK O))
    (hg : g ∈ XiPolZ O N r t b) :
    g ∈ Submodule.span (KK O) (map ι '' (Formalism.GM.M.XiPolZ p N r t b : Set (MvPolynomial (Formalism.GM.M.BVar N r t) ℚ_[p]))) := by
  classical
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hsupp := ((mem_restrictSupport_iff _).1 hg.1) (Finset.mem_coe.2 hμ)
  have h1 : monomial μ (1 : ℚ_[p]) ∈ Formalism.GM.M.XiPolZ p N r t b := by
    refine ⟨?_, ⟨monomial μ 1, by simp⟩⟩
    show monomial μ (1 : ℚ_[p]) ∈ restrictSupport ℚ_[p] _
    rw [mem_restrictSupport_iff]
    intro m hm
    have : m = μ := by
      have := support_monomial_subset hm
      simpa using this
    rw [this]
    exact hsupp
  have h2 : monomial μ (g.coeff μ) = g.coeff μ • map ι (monomial μ (1 : ℚ_[p])) := by
    rw [map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h1, rfl⟩)

def PG {N r : ℕ} (D : BlockData N) (j : Fin (gmB D).T.t → ℕ) (jp : ℕ) :
    MvPolynomial (Formalism.GM.M.BVar N r (gmB D).T.t) ℚ_[p] :=
  (∏ i, (gmB D).Ehat p (r := r) i ^ j i) * (gmB D).Eplus p (r := r) ^ jp *
    (∏ i, X (Formalism.GM.M.scalZ N r (gmB D).T.t (Fin.castSucc i)) ^ (gmB D).T.z i) *
    X (Formalism.GM.M.scalZ N r (gmB D).T.t (Fin.last (gmB D).T.t)) ^ (gmB D).zPlus

theorem finrank_span_image_le (ι : ℚ_[p] →+* KK O) {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℚ_[p] V₁]
    [AddCommGroup V₂] [Module (KK O) V₂] (f : V₁ → V₂) (hadd : ∀ u v, f (u + v) = f u + f v)
    (hsm : ∀ (c : ℚ_[p]) u, f (c • u) = ι c • f u) (W : Submodule ℚ_[p] V₁) [FiniteDimensional ℚ_[p] W] :
    Module.finrank (KK O) (Submodule.span (KK O) (f '' (W : Set V₁))) ≤ Module.finrank ℚ_[p] W := by
  classical
  set bW := Module.finBasis ℚ_[p] W
  have h0 : f 0 = 0 := by
    have := hsm 0 0
    rwa [zero_smul, map_zero, zero_smul] at this
  have hsum : ∀ (s : Finset (Fin (Module.finrank ℚ_[p] W))) (c : Fin (Module.finrank ℚ_[p] W) → ℚ_[p]),
      f (∑ i ∈ s, c i • (bW i : V₁)) = ∑ i ∈ s, ι (c i) • f (bW i) := by
    intro s c
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hsm, ih]
  have hle : Submodule.span (KK O) (f '' (W : Set V₁)) ≤
      Submodule.span (KK O) (Set.range fun i => f (bW i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (⟨w, hw⟩ : W) = ∑ i, (bW.repr ⟨w, hw⟩ i) • bW i := (bW.sum_repr _).symm
    have hw'' : w = ∑ i, (bW.repr ⟨w, hw⟩ i) • (bW i : V₁) := by
      have h3 := congrArg (Submodule.subtype W) hw'
      rw [map_sum] at h3
      simpa only [Submodule.subtype_apply, map_smul] using h3
    rw [hw'', hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional (KK O) (Submodule.span (KK O) (Set.range fun i => f (bW i))) :=
    FiniteDimensional.span_of_finite (KK O) (Set.finite_range _)
  calc Module.finrank (KK O) (Submodule.span (KK O) (f '' (W : Set V₁)))
      ≤ Module.finrank (KK O) (Submodule.span (KK O) (Set.range fun i => f (bW i))) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank ℚ_[p] W)) := finrank_range_le_card _
    _ = Module.finrank ℚ_[p] W := Fintype.card_fin _

theorem finrank_biSup_le {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] (U : ι → Submodule K V)
    (s : Finset ι) (hU : ∀ i ∈ s, FiniteDimensional K (U i)) :
    FiniteDimensional K (⨆ i ∈ s, U i : Submodule K V) ∧
      Module.finrank K (⨆ i ∈ s, U i : Submodule K V) ≤ ∑ i ∈ s, Module.finrank K (U i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), U i) = (⊥ : Submodule K V) by simp]
    exact ⟨inferInstance, by simp⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hU i (Finset.mem_insert_of_mem hi)
    have ha' := hU a (Finset.mem_insert_self a s)
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    refine ⟨Submodule.finiteDimensional_sup _ _, ?_⟩
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left h2 _)

end Dim

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem mem_levels_iff' {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) :
    x ∈ levels G ↔ G.LevelOK x.1 x.2 := by
  unfold levels
  simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨fun i => ?_, ?_⟩, h⟩⟩
  · have hle := Finset.single_le_sum (s := Finset.univ) (f := fun a => G.LL.deg a)
      (fun a _ => Nat.zero_le _) (Finset.mem_univ (⟨min (G.T.pos i) (N - 1), by
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · exact absurd G.uPos.2 (by omega)
        · omega⟩ : Fin N))
    have h1 := (h.1 i).1
    omega
  · have h2 := h.2
    have h3 := min_le_right (G.LL.deg G.uPos) G.B
    omega

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestBClvl : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ l ∈ lv C0 CE1 CE2 X aTop b,
      Module.finrank (KK X.O) (Submodule.span (KK X.O)
        ((blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).gens X.O (r := X.r) l.1 l.2)) ≤
      Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2)

theorem restBCdim_of (h : RestBClvl C0 CE1 CE2 X) : RestBCdim C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hk
  rw [finrank_blockLat X.O X.p X.r (Formalism.MainNotions.G.GLWeightTheory.valuation_properties_hold X.std.1.prime X.setting) (X.S C0 CE1 CE2) aTop aPlus X.m b]
  unfold blockRank
  simp only
  set D := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hD
  have hU : Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
        Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))) ≤
      ⨆ l ∈ lv C0 CE1 CE2 X aTop b, Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) := by
    rw [Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span X.O (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens X.O (r := X.r) j jp) := hx
    refine Submodule.span_induction (p := fun x _ => x ∈ ⨆ l ∈ lv C0 CE1 CE2 X aTop b,
        Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨j, jp, hl, hy⟩ := hy
      have hmem : ((j, jp) : Lv C0 CE1 CE2 X) ∈ lv C0 CE1 CE2 X aTop b := by
        exact (mem_levels_iff' (gB C0 CE1 CE2 X aTop 0 b) (j, jp)).2 hl
      exact (le_iSup₂ (f := fun (l : Lv C0 CE1 CE2 X) (_ : l ∈ lv C0 CE1 CE2 X aTop b) =>
        Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) (j, jp) hmem) (Submodule.subset_span hy)
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [algebra_compatible_smul (KK X.O) a x]
      exact Submodule.smul_mem _ _ hx
  have := span_SSZ_finite (O := X.O) (r := X.r) D
  have hfd : ∀ l ∈ lv C0 CE1 CE2 X aTop b,
      FiniteDimensional (KK X.O) (Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) := by
    intro l hl
    have hsub : Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) ≤
        Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
          Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))) := by
      apply Submodule.span_mono
      intro y hy
      apply Submodule.subset_span
      refine Set.mem_iUnion.2 ⟨l.1, Set.mem_iUnion.2 ⟨l.2, Set.mem_iUnion.2 ⟨?_, hy⟩⟩⟩
      exact (mem_levels_iff' (gB C0 CE1 CE2 X aTop 0 b) l).1 hl
    exact Submodule.finiteDimensional_of_le hsub
  obtain ⟨hfd2, hle⟩ := finrank_biSup_le (fun l : Lv C0 CE1 CE2 X =>
    Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) (lv C0 CE1 CE2 X aTop b) hfd
  calc Module.finrank (KK X.O) (Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
          Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))))
      ≤ Module.finrank (KK X.O) (⨆ l ∈ lv C0 CE1 CE2 X aTop b,
          Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) : Submodule (KK X.O) _) :=
        Submodule.finrank_mono hU
    _ ≤ ∑ l ∈ lv C0 CE1 CE2 X aTop b, Module.finrank (KK X.O) (Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) :=
        hle
    _ ≤ ∑ l ∈ lv C0 CE1 CE2 X aTop b,
          Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) :=
        Finset.sum_le_sum fun l hl => h aTop hT aPlus hP b hk l hl

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
