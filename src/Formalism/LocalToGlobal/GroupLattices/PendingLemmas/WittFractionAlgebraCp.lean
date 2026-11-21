import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ICIntCp
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetOfColSpanEq
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WeightUpdateAtPlace
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.SubstZOfXCoordZA
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetYtMatNeZero

section
noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable (p : ℕ) [hp : Fact p.Prime]

def OcC : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by
    show ‖(1 : ℂ_[p])‖ ≤ 1
    rw [norm_one]
  add_mem' := fun {a b} ha hb => by
    show ‖a + b‖ ≤ 1
    exact le_trans (IsUltrametricDist.norm_add_le_max a b) (max_le ha hb)
  zero_mem' := by
    show ‖(0 : ℂ_[p])‖ ≤ 1
    rw [norm_zero]
    exact zero_le_one
  neg_mem' := fun {a} ha => by
    show ‖-a‖ ≤ 1
    rw [norm_neg]
    exact ha

variable {p}

theorem mem_OcC (x : ℂ_[p]) : x ∈ OcC p ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem OcC_val (x : ℂ_[p]) : x ∈ OcC p ∨ x⁻¹ ∈ OcC p := by
  rcases le_total ‖x‖ 1 with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    show ‖x⁻¹‖ ≤ 1
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ h

theorem norm_p_pos : 0 < ‖(p : ℂ_[p])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)

theorem OcC_rank1 (x : ℂ_[p]) (hx : x ≠ 0) :
    (∃ n : ℕ, (p : ℂ_[p]) ^ n / x ∈ OcC p) ∧ (x⁻¹ ∉ OcC p → ∃ n : ℕ, x ^ n / (p : ℂ_[p]) ∈ OcC p) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  constructor
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx0 (norm_p_lt_one (p := p))
    refine ⟨n, ?_⟩
    show ‖(p : ℂ_[p]) ^ n / x‖ ≤ 1
    rw [norm_div, norm_pow, div_le_one hx0]
    exact hn.le
  · intro h
    have h1 : ‖x‖ < 1 := by
      by_contra hc
      refine h ?_
      show ‖x⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (not_lt.1 hc)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_p_pos (p := p)) h1
    refine ⟨n, ?_⟩
    show ‖x ^ n / (p : ℂ_[p])‖ ≤ 1
    rw [norm_div, norm_pow, div_le_one norm_p_pos]
    exact hn.le

section Emb

variable {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (i : Kf →+* ℂ_[p]) (hi : ∀ x : O, ‖i (algebraMap O Kf x)‖ ≤ 1)

include hi

theorem norm_unit (u : Oˣ) : ‖i (algebraMap O Kf (u : O))‖ = 1 := by
  refine le_antisymm (hi _) ?_
  have h1 : i (algebraMap O Kf (u : O)) * i (algebraMap O Kf ((u⁻¹ : Oˣ) : O)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one] at h2
  calc (1 : ℝ) = ‖i (algebraMap O Kf (u : O))‖ * ‖i (algebraMap O Kf ((u⁻¹ : Oˣ) : O))‖ := h2.symm
    _ ≤ ‖i (algebraMap O Kf (u : O))‖ * 1 := mul_le_mul_of_nonneg_left (hi _) (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_nonunit {y : O} (hy : ¬ IsUnit y) : ‖i (algebraMap O Kf y)‖ < 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hp0 : (p : O) ≠ 0 := by
    intro h0
    have := congrArg (fun z => i (algebraMap O Kf z)) h0
    simp only [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.2 hp.out.ne_zero : (p : ℂ_[p]) ≠ 0) this
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  obtain ⟨u, hu⟩ := he.symm
  have hϖ1 : ‖i (algebraMap O Kf ϖ)‖ < 1 := by
    by_contra hc
    have h1 : ‖i (algebraMap O Kf ϖ)‖ = 1 := le_antisymm (hi _) (not_lt.1 hc)
    have h2 := congrArg (fun t => ‖i (algebraMap O Kf t)‖) hu
    simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h2
    rw [h1, norm_unit i hi u, one_pow, one_mul] at h2
    exact absurd h2.symm (ne_of_lt (norm_p_lt_one (p := p)))
  have hy1 : ϖ ∣ y := by
    have : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal y).2 hy
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    exact this
  obtain ⟨z, rfl⟩ := hy1
  rw [map_mul, map_mul, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hi z)) hϖ1

theorem norm_le_one_iff [IsFractionRing O Kf] (x : Kf) : ‖i x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap O Kf) := by
  constructor
  · intro hx
    rcases ValuationRing.isInteger_or_isInteger O x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨y, hy⟩
    · by_cases hx0 : x = 0
      · exact ⟨0, by rw [hx0, map_zero]⟩
      by_cases hu : IsUnit y
      · obtain ⟨u, rfl⟩ := hu
        refine ⟨((u⁻¹ : Oˣ) : O), ?_⟩
        have h1 : algebraMap O Kf ((u⁻¹ : Oˣ) : O) * algebraMap O Kf (u : O) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        rw [hy] at h1
        exact (eq_of_mul_inv_eq_one h1)
      · exfalso
        have h1 := norm_nonunit i hi hu
        rw [hy, map_inv₀, norm_inv] at h1
        have hpos : 0 < ‖i x‖ := norm_pos_iff.2 ((map_ne_zero i).2 hx0)
        exact absurd h1 (not_lt.2 ((one_le_inv₀ hpos).2 hx))
  · rintro ⟨y, rfl⟩
    exact hi y

end Emb

structure CEmb (G : GAtP p) where
  iK : G.Kf →+* ℂ_[p]
  int : ∀ x : G.O, ‖iK (algebraMap G.O G.Kf x)‖ ≤ 1

theorem CEmb.mem_iff {X : Sys p} (E : CEmb X.G) [IsFractionRing X.G.O X.G.Kf] (x : X.G.Kf) :
    E.iK x ∈ OcC p ↔ x ∈ X.intK := by
  rw [mem_OcC, norm_le_one_iff E.iK E.int]
  rfl

section Conc

variable {n : ℕ} (f : K0 p →+* ℂ_[p]) (hf : ∀ x : WW p, ‖f (algebraMap (WW p) (K0 p) x)‖ ≤ 1)
  (L : IntermediateField (KO p n) (Om p n)) [FiniteDimensional (KO p n) L]

def embLC : L →+* ℂ_[p] := (iC f).comp (gL L)

include hf in
theorem embLC_int (x : OL p n L) : ‖embLC f L (algebraMap (OL p n L) L x)‖ ≤ 1 :=
  (iC_int_Cp f hf _).1 ((Oc_K L _).2 ⟨x, rfl⟩)


end Conc

end Formalism.L2.G.Pend
end
end

section
noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc]
  (ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc)

def volE (v : X.Pl) (j : ℕ) (L : (X.Pj j).Tup) (L' : (X.Pj (j + 1)).Tup) : ℤ :=
  (NN X.G.P.m X.t j : ℤ) * len X v (j + 1) L' - (NN X.G.P.m X.t (j + 1) : ℤ) * len X v j L

abbrev XiTy (v : X.Pl) (j : ℕ) : Type :=
  Aw X v j → ((Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v) → ℚ) →+ MvPowerSeries (X.ZA j) Kc)

def IsXi (v : X.Pl) (j : ℕ) (Ξ : XiTy X Kc v j) : Prop :=
  ∃ u u' : X.G.Kf, X.vEqK u 0 ∧ X.vEqK u' 0 ∧
    ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
      ThF j La La' = (u ^ (len X v j La.2) * u' ^ (len X v (j + 1) La'.2) *
        (p : X.G.Kf) ^ (-(((X.G.P.n' v / 2 : ℕ) : ℤ) * volE X v j La.2 La'.2))) •
        Ξ (aw X v j La La') (X.ind v j La.2 La'.2)

def XiEx (v : X.Pl) (j : ℕ) : Prop := ∃ Ξ : XiTy X Kc v j, IsXi X Kc ThF v j Ξ

def xiOf (v : X.Pl) (j : ℕ) : XiTy X Kc v j := by
  classical exact if h : XiEx X Kc ThF v j then Classical.choose h else fun _ => 0

theorem xiOf_spec {v : X.Pl} {j : ℕ} (h : XiEx X Kc ThF v j) : IsXi X Kc ThF v j (xiOf X Kc ThF v j) := by
  rw [xiOf, dif_pos h]
  exact Classical.choose_spec h

end Formalism.L2.G.Pend
end
end

section
noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

variable {p : ℕ} [Fact p.Prime]

@[reducible] def wittFractionAlgebraCp (p : ℕ) [Fact p.Prime] : Algebra (K0 p) ℂ_[p] := (k0ToC p).toAlgebra

@[reducible] def algKfC {G : GAtP p} (E : CEmb G) : Algebra G.Kf ℂ_[p] := E.iK.toAlgebra

abbrev DelTy (X : Sys p) (E : CEmb X.G) : Type :=
  letI := algKfC E
  ∀ j, (X.Pj j).Xsp →ₗ[X.G.Kf] MvPowerSeries (X.ZA j) ℂ_[p] →ₗ[X.G.Kf] XspC (X.Pj (j + 1)) ℂ_[p]

def DelDeg (X : Sys p) (E : CEmb X.G) (DelF : DelTy X E) : Prop :=
  letI := algKfC E
  ∀ j (G : (X.Pj j).Xsp) (f : MvPowerSeries (X.ZA j) ℂ_[p]),
    (∀ n : X.ZA j →₀ ℕ, (∀ (v : X.Pl) (s : Fin (X.G.P.n' v)),
        ((∑ a, ∑ b, n ⟨v, (s, a, b)⟩ : ℕ) : ℤ) = ∑ i ∈ Finset.Icc 1 (NN X.G.P.m X.t (j + 1)), X.nuv v (j + 1) s i) →
      MvPowerSeries.coeff n f = 0) → DelF j G f = 0

abbrev pendOf (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    (be : MvPowerSeries (Fin 2) (K0 p))
    (ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p])
    (DelF : DelTy X E) (hDel : DelDeg X E DelF) : Pend X :=
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  { Kc := ℂ_[p]
    Oc := OcC p
    Oc_val := OcC_val
    witt_mem_integers_Cp := fun x => by
      show ‖k0ToC p (algebraMap (WW p) (K0 p) x)‖ ≤ 1
      rw [witt_fraction_to_Cp_algebraMap]
      exact norm_wToC_le p x
    Oc_K := fun x => E.mem_iff x
    Oc_rank1 := OcC_rank1
    be := be
    Rep := repOf X.Lv hfin
    Rep_lat := repOf_lat X.Lv hfin
    Rep_ex := fun j _ => repOf_ex X.Lv hfin j
    stab_fin := fun j _ => stab_fin X hst j
    Frm := Frm X
    ThA := fun j La La' φ => thA ℂ_[p] φ (ThF j La La')
    bc := fun _ _ _ φ => bc ℂ_[p] φ
    ThF := ThF
    ThF_frm := fun j La La' φ => thF_frm ℂ_[p] φ (ThF j La La')
    DelF := DelF
    Del_deg := hDel
    len := len X
    len_edge := len_edge X
    len_other := len_other X
    Aw := Aw X
    aw := aw X
    weight_update_at_place := weight_update_at_place X
    aw_tgt := aw_tgt X
    Xi := xiOf X ℂ_[p] ThF }

abbrev pendC (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    (be : MvPowerSeries (Fin 2) (K0 p))
    (ThF : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) ℂ_[p]) : Pend X :=
  letI := algKfC E
  pendOf X E hfin hst be ThF (delF X ℂ_[p]) (del_deg X ℂ_[p])

end Formalism.L2.G.Pend
end
end
