import Formalism.SharpRestriction.Divisibility.OrbitPlaces

section
noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.OrbitPlaces

def ydOf (f : ℕ → ℕ) (hf : Antitone f) (N : ℕ) : YoungDiagram where
  cells := (Finset.range N).biUnion fun r => (Finset.range (f r)).image fun c => (r, c)
  isLowerSet := by
    intro a b hba ha
    simp only [Finset.coe_biUnion, Finset.coe_range, Finset.coe_image, Set.mem_iUnion, Set.mem_image, Set.mem_Iio,
      exists_prop] at ha ⊢
    obtain ⟨r, hr, c, hc, rfl⟩ := ha
    have h1 : b.1 ≤ r := (Prod.le_def.1 hba).1
    have h2 : b.2 ≤ c := (Prod.le_def.1 hba).2
    exact ⟨b.1, lt_of_le_of_lt h1 hr, b.2, lt_of_le_of_lt h2 (lt_of_lt_of_le hc (hf h1)), rfl⟩




def NuIsPart (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (i : ℕ), i < D.R.m → ∀ τ : D.what₂.Tau, ∃ f : ℕ → ℕ, Antitone f ∧
    ∀ r, ((f r : ℕ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) τ r else 0


section NuPart

variable (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau)

def nuE (a : ℕ) : ℚ := if h : a < D.R.m then (D.hc τ).e ⟨a, h⟩ else 0



def nuQ (i r : ℕ) : ℚ :=
  DV.srcPar D u τ r + nuE D τ i - (((D.R.N i : ℕ) : ℚ) + ((D.R.N (i + 1) : ℕ) : ℚ) - 1 - 2 * (r : ℚ)) / 2






theorem nu_last (hk : 0 < D.R.k) :
    ((D.R.t : ℚ) + 3) / 2 < (D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ + nuE D τ 0 := by
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have h1 := (D.hcW u τ).u_last_gt hk hm
  have h2 := (D.hcW u τ).gap_be ⟨0, hm⟩
  have he : nuE D τ 0 = (D.hcW u τ).e ⟨0, hm⟩ := by
    unfold nuE
    rw [dif_pos hm, D.hcW_e u τ]
  rw [he]
  linarith






end NuPart




end Formalism.MainNotions.DIV.Inh

end
end

section
noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

theorem even_add_order_two_le (D : D7) (h : HH D) (hev : Even (addOrderOf h)) : Even (addOrderOf h) ∧ 2 ≤ addOrderOf h := by
  have hfin : Finite (HH D) := Finite.of_fintype (Fin D.R.ord)
  refine ⟨hev, ?_⟩
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  obtain ⟨k, hk⟩ := hev
  omega

theorem orbOK_iff (D : D7) (p : ℕ) : OrbOK D p ↔ 5 ≤ p ∧ (IsSg D p ∨ HEv D p) := by
  constructor
  · rintro ⟨h5, hev, -⟩
    refine ⟨h5, ?_⟩
    by_cases hs : IsSg D p
    · exact Or.inl hs
    · right
      unfold nP at hev
      rw [if_neg hs] at hev
      exact hev
  · rintro ⟨h5, hc⟩
    by_cases hs : IsSg D p
    · have hpos : 0 < addOrderOf (2 • hP D p) := by
        have hfin : Finite (HH D) := Finite.of_fintype (Fin D.R.ord)
        exact addOrderOf_pos _
      refine ⟨h5, ?_, ?_⟩
      · unfold nP
        rw [if_pos hs]
        exact even_two_mul _
      · unfold nP
        rw [if_pos hs]
        omega
    · have hev : HEv D p := hc.resolve_left hs
      obtain ⟨h1, h2⟩ := even_add_order_two_le D (hP D p) hev
      refine ⟨h5, ?_, ?_⟩
      · unfold nP
        rw [if_neg hs]
        exact h1
      · unfold nP
        rw [if_neg hs]
        exact h2

private theorem five_le_of_prime_not_small_not_split (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound)
    (hs : p ∉ D.host.toHostRaw.small) (hj : ¬ jacobiSym (-(D.host.d : ℤ)) p = 1) : 5 ≤ p := by
  by_contra hlt
  have h2 : 2 ≤ p := hp.two_le
  have hne2 : p ≠ 2 := by
    rintro rfl
    apply hs
    have hm : 2 ∈ D.host.toHostRaw.QS.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (dvd_pow_self 2 (by omega)) D.host.tower_dvd,
        D.host.QS_pos.ne'⟩
    exact hm
  have hne4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  obtain rfl : p = 3 := by omega
  exact hj (D.host.split_small 3 hp (by norm_num) h3)

theorem five_le_of_class (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound) (hc : IsResidueClassZero D p ∨ IsSg D p) : 5 ≤ p := by
  have hcls : D.host.cls p = PrimeClass.inertClass ∨ D.host.cls p = PrimeClass.signal := hc
  unfold Formalism.BasicNotions.Host.cls Formalism.BasicNotions.primeClass at hcls
  split_ifs at hcls with a1 a2 a3 a4 a5 <;>
    first
      | exact five_le_of_prime_not_small_not_split D p hp h3 a1 a4
      | simp at hcls

theorem orbOK_of_class (D : D7) (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ D.host.splitBound)
    (hc : (IsResidueClassZero D p ∧ HEv D p) ∨ IsSg D p) : OrbOK D p := (orbOK_iff D p).2 ⟨five_le_of_class D p hp h3 (hc.imp And.left id), hc.elim (fun h => Or.inr h.2) Or.inl⟩

theorem orbit_admissible_of_split_bound (D : D7) (h3 : 3 ≤ D.host.splitBound) : OrbitParityCond D := by
  unfold OrbitParityCond
  exact ⟨fun p hp hc => orbOK_of_class D p hp h3 hc, fun p hp hc => five_le_of_class D p hp h3 (Or.inl hc)⟩






section Shape

variable {D : D7}





variable {L : SizeData₂ D} {X : Inst D L}




end Shape

end Formalism.MainNotions.DIV.Inh

end
end
