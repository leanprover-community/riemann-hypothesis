import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm

section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.heckeAdj :
    UpperTheory.V.Af.Gk.HeckeAdj := by
  intro F _ _ a w V _ _ ρ H hH x hx ϖ hϖ j
  have hK : ∀ k ∈ GlobalTheory.LFun.KGL w a, GlobalTheory.CuspRep.invT a _ k ∈ GlobalTheory.LFun.KGL w a := by
    rintro _ ⟨k, rfl⟩
    exact ⟨GlobalTheory.CuspRep.invT a _ k, InvT.map_invT _ k⟩
  have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
  have hf := fun (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion F)) V) => GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm F w a) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ x
  have e1 := (H.flip x).toAddMonoidHom.map_finsum (hf ρ)
  have e2 := (H x).toAddMonoidHom.map_finsum (hf (ρ.comp (GlobalTheory.CuspRep.invT a (w.adicCompletion F))))
  refine e1.trans ((finsum_congr fun c => ?_).trans e2.symm)
  generalize c.out = g
  change H (_ • ρ g x) x = H x (_ • ρ (GlobalTheory.CuspRep.invT a _ g) x)
  unfold Formalism.UG.Tj
  by_cases hg : g ∈ {g : GL (Fin a) (w.adicCompletion F) | ∃ k ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w),
      ∃ b ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w), g.val = k.val * Formalism.UG.diagJ a ϖ j * b.val}
  · rw [Set.indicator_of_mem hg, Pi.one_apply, one_smul, one_smul]
    obtain ⟨k, hk, b, hb, e⟩ := hg
    obtain ⟨d, rfl⟩ : ∃ d, g = k * d * b := ⟨k⁻¹ * g * b⁻¹, by group⟩
    have hd : d.val = Formalism.UG.diagJ a ϖ j := by
      rw [Units.val_mul, Units.val_mul] at e
      exact (Units.mul_right_inj k).1 ((Units.mul_left_inj b).1 e)
    have hd' : GlobalTheory.CuspRep.invT a _ d = d⁻¹ := by
      rw [← inv_eq_iff_eq_inv]
      apply Units.ext
      rw [InvT.invT_inv_val, hd, Formalism.UG.diagJ, Matrix.diagonal_transpose]
    simp only [map_mul, Module.End.mul_apply, hd']
    rw [hfix b hb, hfix _ (hK b hb)]
    have h1 : H (ρ k (ρ d x)) x = H (ρ d x) x := by
      rw [← hH k (ρ d x) x, hfix k hk]
    have h2 : H x (ρ (GlobalTheory.CuspRep.invT a _ k) (ρ d⁻¹ x)) = H x (ρ d⁻¹ x) := by
      rw [← hH (GlobalTheory.CuspRep.invT a _ k) x (ρ d⁻¹ x), hfix _ (hK k hk)]
    rw [h1, h2, ← hH d x (ρ d⁻¹ x), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  · rw [Set.indicator_of_notMem hg]
    simp
end

section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.satConj :
    UpperTheory.V.Af.Gk.SatConj := by
  intro F _ _ a w V W _ _ _ _ ρ ρ' H C hdef hH hC B hB
  have hK : ∀ k ∈ GlobalTheory.LFun.KGL w a, GlobalTheory.CuspRep.invT a _ k ∈ GlobalTheory.LFun.KGL w a := by
    rintro _ ⟨k, rfl⟩
    exact ⟨GlobalTheory.CuspRep.invT a _ k, InvT.map_invT _ k⟩
  have hB' : GlobalTheory.LFun.HasSatGL w (ρ.comp (GlobalTheory.CuspRep.invT a (w.adicCompletion F))) (B.map (·⁻¹)) :=
    InvT.hasSatGL_invT (ρ := ρ) (LinearEquiv.refl ℂ V) (fun _ _ => rfl) hB
  have key : ∀ x ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w a), x ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w ρ' (C x) (B.map (·⁻¹)) := by
    intro x hx h0
    have hfix := GlobalTheory.LGrp.mem_fixed.1 hx
    have h1 := hB.2 x hx h0
    have h2 := hB'.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => hfix _ (hK k hk)) h0
    refine ⟨(map_ne_zero_iff C C.injective).2 h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hC, hfix k hk],
      h2.2.2.1, fun ϖ hϖ j hj => ?_⟩
    have e := heckeAdj F a w V ρ H hH x hx ϖ hϖ j
    rw [h1.2.2.2 ϖ hϖ j hj, h2.2.2.2 ϖ hϖ j hj, H.map_smulₛₗ, (H x).map_smul, LinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul] at e
    have e' := mul_right_cancel₀ (fun h => h0 (hdef x h)) e
    rw [← e', ← C.map_smulₛₗ, ← h1.2.2.2 ϖ hϖ j hj]
    refine ((C.toLinearMap.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm F w a)
      (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ x)).trans (finsum_congr fun c => ?_)).symm
    generalize c.out = g
    change C (_ • ρ g x) = _ • ρ' g (C x)
    rw [C.map_smulₛₗ, hC]
    congr 1
    unfold Formalism.UG.Tj
    by_cases hg : g ∈ {g : GL (Fin a) (w.adicCompletion F) | ∃ k ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w),
        ∃ b ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.Ov F w), g.val = k.val * Formalism.UG.diagJ a ϖ j * b.val}
    · rw [Set.indicator_of_mem hg, Pi.one_apply, map_one]
    · rw [Set.indicator_of_notMem hg, map_zero]
  constructor
  · obtain ⟨x, hx⟩ := hB.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx.2.1 hx.1).2.1, (key x hx.2.1 hx.1).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := C.surjective y
    refine key x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => C.injective ?_) ((map_ne_zero_iff C C.injective).1 h0)
    rw [hC, GlobalTheory.LGrp.mem_fixed.1 hy k hk]
end
