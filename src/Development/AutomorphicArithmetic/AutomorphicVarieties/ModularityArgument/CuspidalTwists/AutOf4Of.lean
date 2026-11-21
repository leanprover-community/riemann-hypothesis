import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.DefsBad
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.IrrIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Cu

private theorem gd_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (h : p.Coprime q)
    (hq : A.valuation (q : Ω) < 1) : ¬ A.valuation (p : Ω) < 1 := fun hp => by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hv : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n => (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have h1 : A.valuation ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv a)) hp
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv b)) hq
  have h2 : (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem gd_rb {D : Raw Ω c} (T : Tower D) (g : G T.F Ω) :
    T.rb wAl g = residue c.O (D.al (resQ T.F g) : c.O) := by
  have e : chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹ = D.al (resQ T.F g) := by
    generalize resQ T.F g = s
    cases T.pr <;> simp [chi, lab, Raw.ps, Raw.th, mul_comm]
  show residue c.O (((chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (1 : ℤ) *
    (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (0 : ℤ) : c.Oˣ) : c.O) = _
  rw [zpow_one, zpow_zero, mul_one, e]

private theorem gd_al (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) (hg : D.ξ g = 1) :
    residue c.O (D.al g : c.O) = 1 := by
  have e : D.al g * D.om g = chiO ℚ Ω l c.O g := by
    simp only [Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, hg, mul_one, inv_mul_cancel_right]
  have e2 := congrArg (fun u : c.Oˣ => residue c.O (u : c.O)) e
  simp only [Units.val_mul, map_mul] at e2
  have e3 : residue c.O (D.om g : c.O) = residue c.O (chiO ℚ Ω l c.O g : c.O) := hD.om_bar g
  rw [← e3] at e2
  have hu : IsUnit (residue c.O (D.om g : c.O)) := (D.om g).isUnit.map _
  exact (mul_eq_right₀ hu.ne_zero).1 e2

private theorem gd_rbar (D : Raw Ω c) (g : G ℚ Ω) (h : D.rbar g = 1) : residue c.O (D.al g : c.O) = 1 := by
  have key : D.rbar g 2 2 = residue c.O (Matrix.diagonal (fun i => (D.ps i g : c.O)) 2 2) := rfl
  rw [h, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at key
  exact key.symm

private theorem gd_up {F : IntermediateField ℚ Ω} {g : G ℚ Ω} (hg : g ∈ F.fixingSubgroup) : ∃ g' : G F Ω, resQ F g' = g :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => (F.mem_fixingSubgroup_iff g).1 hg x.1 x.2, rfl⟩

end

theorem UpperTheory.V.Cu.goodOf4 :
    UpperTheory.V.Cu.GoodOf4 := by
  intro Ω _ _ _ l _ c D T₀ T hD hT K' hS hoff w θ hw hsp hθ k g0 ρ c₁ h ρ₁ x hM p hp
  have hK : ∀ g : G T₀.F Ω, residue c.O (D.al (resQ T₀.F g) : c.O) = 1 → resQ T₀.F g ∈ K'.fixingSubgroup := by
    intro g hg
    by_contra hn
    have := (UpperTheory.V.Ws.P1.coefRes c).2.1
    exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq (ResidueField c.O) l]; exact hD.l_odd)
      ((hoff g hn).symm.trans ((gd_rb T₀ g).trans hg))
  by_cases hpS : p ∈ D.S
  · exact Or.inl (hS p hpS)
  by_cases hpw : p = w
  · subst hpw
    refine Or.inl fun A hA g hg => ?_
    obtain ⟨⟨h1, h2⟩, -⟩ := hsp A hA hg
    obtain ⟨g', rfl⟩ := gd_up h1
    exact hK g' (gd_rbar D _ h2)
  refine Or.inr ⟨fun e => hpS (e ▸ hD.l_mem), fun A hA s hs => ?_⟩
  have hAS : Raw.Away D.S A := fun q hq =>
    gd_val A ((Nat.coprime_primes (hD.S_prime q hq) hp).2 fun e => hpS (e ▸ hq)) hA
  have hAw : Raw.Away {w} A := fun q hq => by
    rw [Finset.mem_singleton.1 hq]
    exact gd_val A ((Nat.coprime_primes hw hp).2 fun e => hpw e.symm) hA
  have hI : resQ T.L s ∈ Ine (F := ℚ) A := ⟨hs.1, hs.2⟩
  have hξ : D.ξ (resQ T.L s) = 1 := hD.xi_unr A hAS hI
  have hψ : D.ψ (resQ T.L s) = 1 := hD.psi_unr A hAS hI
  have hres : resQ T₀.F (resLe (hT.le.trans T.F_le) s) = resQ T.L s := AlgEquiv.ext fun _ => rfl
  refine ⟨?_, ?_⟩
  · rw [← hres]
    exact hK _ (by rw [hres]; exact gd_al D hD _ hξ)
  · have hφ : phi D T₀.pr (resQ T.L s) = 1 := by
      generalize resQ T.L s = g at hξ hψ
      unfold phi
      split_ifs <;> simp [hξ, hψ]
    have h1 := hM.away A (hAS l hD.l_mem) _ hI hφ (hθ A hAw hI)
    obtain ⟨u, hu⟩ := hM.iso
    have h2 := hu (resQ T.L s)
    have h3 : (mapRep (algebraMap c₁.O (PadicAlgCl l)) ρ₁).toHomUnits (resQ T.L s) = 1 := by
      refine Units.ext ?_
      show (ρ₁ (resQ T.L s)).map (algebraMap c₁.O (PadicAlgCl l)) = 1
      rw [h1]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [h3] at h2
    have h4 : ρ (resQ T.L s) = u⁻¹ * (u * ρ (resQ T.L s) * u⁻¹) * u := by group
    rw [h4, ← h2, mul_one, inv_mul_cancel]
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3 UpperTheory.V.Cu

namespace UpperTheory.V.Cu.AutomorphyOfRankFourLift

theorem irr_cover {H H' K : Type} [Group H] [Group H'] [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (r : H →* Matrix n n K) (r' : H' →* Matrix n n K) (h : ∀ x, ∃ y, ∃ u : K, r x = u • r' y) (hr : Irr r) :
    Irr r' := by
  unfold Irr at hr ⊢
  rw [eq_top_iff, ← hr, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, u, e⟩ := h x
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem q_apply (d : Dat Ω l) (T : Tower d.D) (g : G T.F Ω) :
    ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r g =
      ((toB d.δ (resQ T.F g) : (Qbar l)ˣ) : Qbar l) •
        mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ) (resQ T.F g) := by
  ext i j
  simp only [PD.map_r, Matrix.map_apply, Dat.Q, MonoidHom.comp_apply, mapRep_apply, Matrix.smul_apply, smul_eq_mul,
    rep4, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply, Units.val_one, one_smul, map_mul]
  rfl

end UpperTheory.V.Cu.AutomorphyOfRankFourLift

open UpperTheory.V.Cu.AutomorphyOfRankFourLift in
theorem UpperTheory.V.Cu.autOf4_of (hne : AlNe) : AutOf4 := by
  intro Ω _ _ _ l _ d T hT hok hirr
  have h1 : Irr ((mapRep (algebraMap d.c₁.O (PadicAlgCl l)) (rep4 1 d.ρ₁ d.τ)).comp (resQ T.L)) := by
    refine irr_cover _ _ (fun x => ?_) hirr
    have hfix : ∀ z ∈ T.L, (x : G T.F Ω) z = z := by
      intro z hz
      have hz' : z ∈ T.F ⊔ T.K := T.hL ▸ hz
      have hle : T.F ⊔ T.K ≤ IntermediateField.fixedField (Subgroup.zpowers (resQ T.F x)) := by
        rw [sup_le_iff, IntermediateField.le_iff_le, IntermediateField.le_iff_le, Subgroup.zpowers_le,
          Subgroup.zpowers_le]
        refine ⟨?_, x.2.1⟩
        rw [IntermediateField.mem_fixingSubgroup_iff]
        exact fun y hy => x.1.commutes ⟨y, hy⟩
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hz') _ (Subgroup.mem_zpowers _)
    let y : G T.L Ω := { (x : G T.F Ω).toRingEquiv with commutes' := fun z => hfix z.1 z.2 }
    refine ⟨y, ((toB d.δ (resQ T.F x) : (Qbar l)ˣ) : Qbar l), ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, q_apply,
      show resQ T.L y = resQ T.F (x : G T.F Ω) from AlgEquiv.ext fun _ => rfl]
    rfl
  have hL : IsIrr ((tenB d.ρ₁ d.τ).comp (resQ T.L)) := by
    have := ((irrIff (Qbar l)).1 _).1 h1
    convert this using 1
    ext g : 2
    rfl
  have hkL : ¬ d.K' ≤ T.L := fun hle => by
    obtain ⟨g, hg, hn⟩ := hne Ω l d T hT hok
    refine hn (IntermediateField.fixingSubgroup_le hle ?_)
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => g.commutes ⟨y, hy⟩, hg.1⟩
  haveI : Algebra.IsQuadraticExtension ℚ T.K := { finrank_eq_two' := T.degK }
  have hK : IsAbelianGalois ℚ T.K := IsAbelianGalois.of_isCyclic ℚ T.K
  have hLa : IsAbelianGalois ℚ T.L := by
    have h := @GroundTheory.Global.isAbelianGalois_sup ℚ Ω _ _ _ _ T.F T.K
      T.nF.to_finiteDimensional T.nK.to_finiteDimensional T.abF hK
    rw [← T.hL] at h
    exact h
  obtain ⟨π, hreg, hatt⟩ := d.aut T.L hLa hkL
    (goodOf4 Ω l d.c d.D d.T₀ T d.ctx.1 hT d.K' d.quad.splS d.quad.off d.w d.θ d.wp d.wsp d.wunr d.k _ d.ρ d.c₁ d.h d.ρ₁ d.x d.mod) hL
  refine ⟨π, hreg, ?_⟩
  have key : Af.tw (((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r.comp (resLe T.F_le)).toHomUnits
      ((toB d.δ).comp (resQ T.L))⁻¹ = (tenB d.ρ₁ d.τ).comp (resQ T.L) := by
    ext g : 2
    rw [tw_val]
    change _ • ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))).r (resLe T.F_le g) = _
    rw [q_apply, smul_smul]
    simp only [MonoidHom.inv_apply, MonoidHom.comp_apply]
    rw [show resQ T.F (resLe T.F_le g) = resQ T.L g from AlgEquiv.ext fun _ => rfl, Units.inv_mul, one_smul]
    rfl
  rw [key]
  exact hatt
end
end
