import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CommensurableK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.InterIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ScalePairMulMulEq
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RelIndexEqAbsDetReal

section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

theorem sqrtNeg_sq (d : ℕ) :
    (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = -(d : ℂ) := by
  have h : ((Real.sqrt d : ℝ) : ℂ) * ((Real.sqrt d : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  linear_combination (Complex.I * Complex.I) * h + (d : ℂ) * Complex.I_mul_I

theorem sqrtNeg_conj (d : ℕ) :
    conj (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) = -(Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]

theorem InK.conj {d : ℕ} {z : ℂ} (hz : InK d z) : InK d (conj z) := by
  obtain ⟨p, q, rfl⟩ := hz
  refine ⟨p, -q, ?_⟩
  rw [map_add, map_mul, sqrtNeg_conj, map_ratCast, map_ratCast]
  push_cast
  ring

def fieldK (d : ℕ) : Subfield ℂ where
  carrier := {z | InK d z}
  mul_mem' := by
    rintro _ _ ⟨p, q, rfl⟩ ⟨p', q', rfl⟩
    refine ⟨p * p' - d * q * q', p * q' + q * p', ?_⟩
    push_cast
    linear_combination ((q : ℂ) * (q' : ℂ)) * sqrtNeg_sq d
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨p, q, rfl⟩ ⟨p', q', rfl⟩
    exact ⟨p + p', q + q', by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨p, q, rfl⟩
    exact ⟨-p, -q, by push_cast; ring⟩
  inv_mem' := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      exact ⟨0, 0, by simp⟩
    have hc0 : conj z ≠ 0 := by simpa using hz0
    obtain ⟨p, q, rfl⟩ := hz
    have hc : conj ((p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))
        = (p : ℂ) - (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
      rw [map_add, map_mul, sqrtNeg_conj, map_ratCast, map_ratCast]
      ring
    rw [hc] at hc0
    have hN : ((p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))
        * ((p : ℂ) - (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ))) = ((p * p + d * q * q : ℚ) : ℂ) := by
      push_cast
      linear_combination (-(q : ℂ) * (q : ℂ)) * sqrtNeg_sq d
    have hN0 : ((p * p + d * q * q : ℚ) : ℂ) ≠ 0 := by
      rw [← hN]
      exact mul_ne_zero hz0 hc0
    refine ⟨p / (p * p + d * q * q), -q / (p * p + d * q * q), ?_⟩
    apply inv_eq_of_mul_eq_one_right
    have : ((p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))
        * (((p / (p * p + d * q * q) : ℚ) : ℂ) + ((-q / (p * p + d * q * q) : ℚ) : ℂ)
          * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))
        = (((p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))
        * ((p : ℂ) - (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ)))) / ((p * p + d * q * q : ℚ) : ℂ) := by
      rw [Rat.cast_div, Rat.cast_div, Rat.cast_neg]
      ring
    rw [this, hN, div_self hN0]

def PD {n : Type*} [Fintype n] (h : Matrix n n ℂ) : Prop :=
  ∀ x : n → ℂ, x ≠ 0 → 0 < (∑ i, ∑ j, x i * h i j * conj (x j)).re

end Formalism.L2.Th1.H
end
end

section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Index

variable {V : Type*} [AddCommGroup V]

theorem relIndex_ne_zero_of_nsmul_mem (H F : AddSubgroup V) [Module.Finite ℤ F] (N : ℕ) (hN : 0 < N)
    (h : ∀ x ∈ F, N • x ∈ H) : H.relIndex F ≠ 0 := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨k, φ, hφ⟩ := Module.Finite.exists_fin' ℤ F
  let ψ : (Fin k → ℤ) →+ (Fin k → ZMod N) := AddMonoidHom.compLeft (Int.castAddHom (ZMod N)) (Fin k)
  have hle : ψ.ker ≤ (H.addSubgroupOf F).comap φ.toAddMonoidHom := by
    intro x hx
    have hx' := (AddMonoidHom.mem_ker).1 hx
    have hdiv : ∀ i, (N : ℤ) ∣ x i := by
      intro i
      have hi := congrFun hx' i
      simpa [ψ, AddMonoidHom.compLeft, ZMod.intCast_zmod_eq_zero_iff_dvd] using hi
    choose y hy using hdiv
    have hxy : x = (N : ℤ) • y := by
      funext i
      simp [hy i]
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hxy]
    have hφy : φ.toAddMonoidHom ((N : ℤ) • y) = N • φ y := by
      rw [LinearMap.toAddMonoidHom_coe, map_zsmul, natCast_zsmul]
    rw [hφy, AddSubgroup.coe_nsmul]
    exact h _ (φ y).2
  have h1 : ψ.ker.index ≠ 0 := by
    haveI : Finite ((Fin k → ℤ) ⧸ ψ.ker) :=
      Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange ψ).symm.toEquiv
    exact AddSubgroup.index_ne_zero_of_finite
  have h2 : ((H.addSubgroupOf F).comap φ.toAddMonoidHom).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero h1 (AddSubgroup.index_dvd_of_le hle)
  rw [AddSubgroup.index_comap_of_surjective _ hφ] at h2
  exact h2

def nsmulHom [Module ℂ V] (N : ℕ) : V →+ V where
  toFun x := N • x
  map_zero' := smul_zero _
  map_add' _ _ := smul_add _ _ _



end Index

section Lattice

instance periodLattice_finite (L : PeriodPair) : Module.Finite ℤ L.lattice := ZLattice.module_finite ℝ L.lattice

def stdLatEquiv (L : PeriodPair) (m : Type*) : stdLat L m ≃+ (m → L.lattice) where
  toFun x := fun i => ⟨(x : m → ℂ) i, (mem_stdLat L m x).1 x.2 i⟩
  invFun y := ⟨fun i => (y i : ℂ), (mem_stdLat L m _).2 fun i => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem stdLat_finite (L : PeriodPair) (m : Type*) [Finite m] : Module.Finite ℤ (stdLat L m) := Module.Finite.equiv (stdLatEquiv L m).symm.toIntLinearEquiv


theorem cmPair_mul_mem (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (k : ℂ) (hk : InK d k) :
    ∃ N : ℕ, 0 < N ∧ ∀ z ∈ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice,
      (N : ℂ) * k * z ∈ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice := by
  obtain ⟨p, q, rfl⟩ := hk
  have hs : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) * ((Real.sqrt (d : ℝ) : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have hδ2 : (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))
      = -(d : ℂ) := by
    linear_combination (Complex.I * Complex.I) * hs + (d : ℂ) * Complex.I_mul_I
  have hpP : (p : ℂ) * (p.den : ℂ) = (p.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num p
  have hqQ : (q : ℂ) * (q.den : ℂ) = (q.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num q
  refine ⟨2 * a * p.den * q.den, by positivity, ?_⟩
  intro z hz
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hz
  rw [PeriodPair.mem_lattice]
  refine ⟨m * (2 * a * q.den * p.num - 2 * a * p.den * q.num * b) + n * (-(p.den * q.num * (b ^ 2 + d))),
    m * (2 * a * (2 * a * p.den * q.num)) + n * (2 * a * q.den * p.num + 2 * a * p.den * q.num * b), ?_⟩
  simp only [Formalism.L2.Th1.F.cmPair, Formalism.L2.Th1.F.cmTheta]
  push_cast
  linear_combination
    (-((m : ℂ) * a + n * ((b + Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) / 2)) * (2 * a * q.den)) * hpP
    - ((m : ℂ) * a + n * ((b + Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) / 2))
        * (2 * a * p.den * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) * hqQ
    - ((a : ℂ) * p.den * q.num * n) * hδ2

theorem cmL_mul_mem (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) (k : ℂ)
    (hk : InK d k) : ∃ N : ℕ, 0 < N ∧ ∀ z ∈ (cmL a b d ha hd lam hlam).lattice,
      (N : ℂ) * k * z ∈ (cmL a b d ha hd lam hlam).lattice := by
  obtain ⟨N, hN, hmul⟩ := cmPair_mul_mem a b d ha hd k hk
  refine ⟨N, hN, fun z hz => ?_⟩
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hz
  have h0 : ((m : ℂ) * (Formalism.L2.Th1.F.cmPair a b d ha hd).ω₁ + n * (Formalism.L2.Th1.F.cmPair a b d ha hd).ω₂)
      ∈ (Formalism.L2.Th1.F.cmPair a b d ha hd).lattice :=
    PeriodPair.mem_lattice.2 ⟨m, n, rfl⟩
  obtain ⟨m', n', hmn⟩ := PeriodPair.mem_lattice.1 (hmul _ h0)
  rw [PeriodPair.mem_lattice]
  refine ⟨m', n', ?_⟩
  simp only [cmL, Formalism.L2.Th1.F.scalePair]
  linear_combination lam * hmn

theorem entries_bound (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
    {m : Type*} [Fintype m] [DecidableEq m] (f : (m → ℂ) →ₗ[ℂ] (m → ℂ))
    (hf : ∀ w w', InK d (f (Pi.single w' 1) w)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ stdLat (cmL a b d ha hd lam hlam) m, N • f x ∈ stdLat (cmL a b d ha hd lam hlam) m := by
  classical
  choose Nf hNf hmem using fun p : m × m => cmL_mul_mem a b d ha hd lam hlam _ (hf p.1 p.2)
  refine ⟨∏ p, Nf p, Finset.prod_pos fun p _ => hNf p, fun x hx => ?_⟩
  rw [mem_stdLat] at hx ⊢
  intro w
  have hfx : f x w = ∑ w', x w' * f (Pi.single w' 1) w := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [show (Pi.single w' (x w') : m → ℂ) = x w' • (Pi.single w' (1 : ℂ) : m → ℂ) by
      ext j; simp [Pi.single_apply]]
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
  show (∏ p, Nf p) • f x w ∈ _
  rw [hfx, Finset.smul_sum]
  refine Submodule.sum_mem _ fun w' _ => ?_
  have h1 := hmem (w, w') (x w') (hx w')
  obtain ⟨r, hr⟩ : Nf (w, w') ∣ ∏ p, Nf p := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  rw [hr]
  have hre : (Nf (w, w') * r) • (x w' * f (Pi.single w' 1) w)
      = r • ((Nf (w, w') : ℂ) * f (Pi.single w' 1) w * x w') := by
    rw [nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [hre]
  exact nsmul_mem h1 r

end Lattice



end Formalism.L2.Th1.H
end
end
