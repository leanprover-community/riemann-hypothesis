module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq

@[expose] public section

namespace GlobalTheory.NatSmulMemLattice

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ (n : ℕ) (a : 𝓞 E), 0 < n ∧ (a : E) = (n : E) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  have h2 : IsIntegral ℤ ((y : E) * (y • c)) := by
    have h3 : IsIntegral ℤ (y : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := y))
    exact h3.mul hy
  refine ⟨y.natAbs * y.natAbs, ⟨_, h2⟩, ?_, ?_⟩
  · have := Int.natAbs_pos.2 hy0
    positivity
  · have h4 : ((y.natAbs * y.natAbs : ℕ) : E) = (y : E) * (y : E) := by
      have h5 : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := Int.natAbs_mul_self
      have h6 := congrArg (Int.cast : ℤ → E) h5
      rw [Int.cast_natCast, Int.cast_mul] at h6
      exact h6
    rw [h4]
    change (y : E) * (y • c) = _
    rw [zsmul_eq_mul, mul_assoc]

theorem exists_nat_smul_mem_lattice {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (v : Formalism.BasicNotions.HSpace.V V) :
    ∃ d : ℕ, 0 < d ∧ (d : 𝓞 (Formalism.BasicNotions.D7.host D).E) • v ∈ Formalism.BasicNotions.HSpace.L0 V :=
  by
    let E := (Formalism.BasicNotions.D7.host D).E
    let f := (V.hT v).restrictScalars (𝓞 E)
    obtain ⟨d, hd, hint⟩ := FractionalIdeal.isFractional_of_fg
      (S := nonZeroDivisors (𝓞 E)) (V.standardTuple_isLattice.fg.map f)
    have hd0 : (d : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
    obtain ⟨n, a, hn, ha⟩ := exists_nat_mul_integral (d : E)⁻¹
    refine ⟨n, hn, ?_⟩
    rw [← V.baseLattice_isUnimodular]
    change (n : 𝓞 E) • v ∈ Formalism.E.hdual V.hT V.L0
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
    intro y hy
    obtain ⟨b, hb⟩ := hint (V.hT v y) ⟨y, hy, rfl⟩
    have hb' : (b : E) = (d : E) * V.hT v y := hb
    have hab : ((a * b : 𝓞 E) : E) = (n : E) * V.hT v y := by
      change (a : E) * (b : E) = _
      rw [ha, hb']
      field_simp
    have hs : IsIntegral ℤ (star ((n : E) * V.hT v y)) := by
      rw [← hab]
      exact (a * b).2.map (starRingEnd E).toIntAlgHom
    apply Submodule.mem_one.2
    refine ⟨⟨_, ?_⟩, rfl⟩
    change IsIntegral ℤ _
    have hh := V.herm.eq y v
    simp only [star_mul, star_natCast] at hs
    have hh' : star (V.hT v y) = V.hT y v := by
      rw [← hh]
      exact star_star _
    rw [hh'] at hs
    simpa [map_smul, Algebra.smul_def, mul_comm] using hs

end GlobalTheory.NatSmulMemLattice
