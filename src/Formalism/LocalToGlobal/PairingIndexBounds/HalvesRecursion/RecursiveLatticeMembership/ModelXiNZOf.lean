import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.Statement
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.MovesComposeU

section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem HfS_apply (D : D7) (T : Tor D) (N N' : ℕ) (z w : VC D N N') : HfS D T N N' z w = Hf D T z w := rfl

theorem al_pm (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : al D T x = 1 ∨ al D T x = -1 := by
  unfold al
  rcases Int.even_or_odd (round (Real.sqrt D.host.d / 2 * (Hf D T x x).re)) with h | h
  · left; exact h.neg_one_zpow
  · right; exact h.neg_one_zpow

theorem exp_int_sign (b : ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I * (b : ℂ))) = Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ)) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨-b, by push_cast; ring⟩

theorem local_global_comparison_holds : Bridge := by
  intro D T N N'
  refine ⟨fun x y => ?_, fun x G => rfl, fun La₁ La₂ G => ?_, fun La' G hG => ?_, fun La' hI => ?_⟩
  · show Hf D T y x = starRingEnd ℂ (Hf D T x y)
    exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T x y
  · funext z
    simp only [Iop, inter, relIdx, AddSubgroup.relIndex]
    rfl
  · intro x hx z
    exact hG.2 x hx z
  · refine ⟨fun x _ => al_pm D T x, fun x hx y hy => ?_⟩
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.semiChar_of_HfInt T hI x hx y hy
    rw [h]
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    have him : (Hf D T x y).im = b := by rw [hab]; simp
    simp only [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf, altE, HfS_apply, him]
    have e := exp_int_sign b
    push_cast at e ⊢
    rw [e]

end Formalism.L2.PairingIndexBounds.Rec
end
end

section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem eqOff_refl (D : D7) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : EqOff D P L L :=
  ⟨0, fun a b _ _ => ⟨fun x hx => L.smul_mem _ hx, fun x hx => L.smul_mem _ hx⟩⟩

theorem volP_self (D : D7) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {N N' : ℕ}
    (Y : AddSubgroup (Matrix (Fin N') (Fin N) (EP D P))) : volP Y Y = 1 := by
  simp [volP, AddSubgroup.addSubgroupOf_self]

theorem volA_pos {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ₀ Λ₁ : AddSubgroup V)
    (hH : IsHerm H) (hA : IsSemiChar H A α) (hB : IsSemiChar H B α) (g0 : GoodLat H α A B Λ₀)
    (g1 : GoodLat H α A B Λ₁) (hfin : relIdx Λ₀ Λ₁ ≠ 0) : 0 < volA A Λ₀ Λ₁ := by
  obtain ⟨hbc, hheis⟩ := heisU V H α A B hH hA hB
  obtain ⟨hfa, hfb⟩ := fixed_of_good H α A B Λ₀ g0 0 (fixedBy H α Λ₀).zero_mem
  obtain ⟨Xi, hXi, -⟩ := xiExists ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
    (Λ₀.addSubgroupOf A) 0 hfa hfb
  obtain ⟨-, hpos, -⟩ := movesU V H α A B Λ₀ Λ₁ hH hA hB g0 g1 hfin 0 (fixedBy H α Λ₀).zero_mem Xi hXi
  exact hpos

theorem modelXiNZ_of (hH : HalvesRec) (D : D7) : ModelXiNZ D := by
  intro cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP th hth
  classical
  obtain ⟨hHerm, -, hIop, hTh, -⟩ := local_global_comparison_holds D (tor0 D cc δ) N N'
  let ι : Type := {q : Pair D N N' // admitted D N N' q.1 q.2 ∧ EqOff D P q.1 L₀ ∧ EqOff D P q.2 L₀'}
  have hfam := genModelXi (VC D N N') (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ))
    (La D (tor0 D cc δ) L₀ L₀') (Matrix (Fin N') (Fin N) (EP D P)) ι
    (fun i => La D (tor0 D cc δ) i.1.1 i.1.2) (fun i => (YP D P i.1.1 i.1.2 : Set _))
    (fun i => volP (YP D P L₀ L₀') (YP D P i.1.1 i.1.2)) hHerm th (hTh _ hth) ?_
  swap
  · intro s
    obtain ⟨A, B, φ, hA, hB, g0, hs⟩ := hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP
      (s.map ⟨Subtype.val, Subtype.val_injective⟩) (by
        intro q hq
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hq
        exact i.2)
    refine ⟨A, B, φ, hA, hB, g0, fun i hi => ?_⟩
    exact hs i.1 (Finset.mem_map_of_mem _ hi)
  obtain ⟨Xi, hXi⟩ := hfam
  refine ⟨Xi, ?_, ?_⟩
  · have h0 := hXi ⟨(L₀, L₀'), hAdm, eqOff_refl D P L₀, eqOff_refl D P L₀'⟩
    simp only [volP_self, Real.sqrt_one, Complex.ofReal_one, one_smul] at h0
    rw [h0]
    obtain ⟨A, B, φ, hA, hB, g0, -⟩ := hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP ∅ (by simp)
    exact interSelf (VC D N N') (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) _ hHerm g0.1 th (hTh _ hth)
  · intro L L' hLL hE1 hE2
    let i : ι := ⟨(L, L'), hLL, hE1, hE2⟩
    have h1 := hXi i
    obtain ⟨A, B, φ, hA, hB, g0, hs⟩ := hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP {(L, L')} (by simpa using ⟨hLL, hE1, hE2⟩)
    obtain ⟨g1, hfin, -, hvol⟩ := hs (L, L') (Finset.mem_singleton_self _)
    have hpos : 0 < volP (YP D P L₀ L₀') (YP D P L L') := by
      rw [hvol]; exact volA_pos _ _ A B _ _ hHerm hA hB g0 g1 hfin
    have hs0 : (Real.sqrt (volP (YP D P L₀ L₀') (YP D P L L')) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
    rw [hIop]
    funext z
    have h1z := congrFun h1 z
    simp only [Pi.smul_apply, smul_eq_mul] at h1z
    change Xi (Set.indicator (YP D P L L' : Set _) 1) z = _ at h1z
    rw [h1z, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]

theorem modelXi_of (hH : HalvesRec) (D : D7) (hΔ : DiscrNZ D) : modelXi D := by
  intro cc δ hcc hδ N N' L₀ L₀' hAdm P hP th hth
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hΔ cc hcc
    rw [← hδ, h0]
    norm_num
  exact modelXiNZ_of hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP th hth

end Formalism.L2.PairingIndexBounds.Rec
end
end
