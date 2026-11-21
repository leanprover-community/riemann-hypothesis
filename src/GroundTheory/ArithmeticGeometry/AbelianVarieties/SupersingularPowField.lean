import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogenyExists

section
namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine

universe u

section Defs

variable {F : Type u} [Field F] [DecidableEq F] (E : WeierstrassCurve F) (p : ℕ)

def IsSupersingular : Prop :=
  ∀ P : E.toAffine.Point, p • P = 0 → P = 0

def IsOrdinary : Prop :=
  ¬ IsSupersingular E p

end Defs

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] (E : WeierstrassCurve F)
  [E.IsElliptic] (p : ℕ) [hp : Fact p.Prime] [CharP F p]

omit [IsAlgClosed F] [E.IsElliptic] hp [CharP F p] in

theorem mem_torsionBy_natCast_iff (n : ℕ) (P : E.toAffine.Point) :
    P ∈ AddSubgroup.torsionBy E.toAffine.Point (n : ℤ) ↔ n • P = 0 :=
  AddSubgroup.torsionBy.nsmul_iff

omit hp [CharP F p] in

theorem finite_torsionBy_natCast {n : ℕ} (hn : n ≠ 0) :
    Finite (AddSubgroup.torsionBy E.toAffine.Point (n : ℤ)) := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  refine Finite.of_injective (fun P : AddSubgroup.torsionBy E.toAffine.Point (n : ℤ) =>
    (⟨P.1, ?_⟩ : (mulIsogeny E n hn').pointHom.ker)) ?_
  · rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny, natCast_zsmul]
    exact (mem_torsionBy_natCast_iff E n P.1).mp P.2
  · intro P Q h
    apply Subtype.ext
    exact congrArg (fun x : (mulIsogeny E n hn').pointHom.ker => (x : E.toAffine.Point)) h

omit [IsAlgClosed F] in

theorem card_torsionBy_prime_lt :
    Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) < p ^ 2 := by
  have h := card_torsion_lt E p
  rwa [← Nat.card_congr (Equiv.subtypeEquivRight fun P => Submodule.mem_torsionBy_iff _ _)] at h


omit [IsAlgClosed F] [E.IsElliptic] hp [CharP F p] in
theorem isSupersingular_iff_torsionBy_eq_bot :
    IsSupersingular E p ↔ AddSubgroup.torsionBy E.toAffine.Point (p : ℤ) = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro P hP
    exact (AddSubgroup.mem_bot).mpr (h P ((mem_torsionBy_natCast_iff E p P).mp hP))
  · intro h P hP
    have : P ∈ AddSubgroup.torsionBy E.toAffine.Point (p : ℤ) := (mem_torsionBy_natCast_iff E p P).mpr hP
    rw [h] at this
    exact (AddSubgroup.mem_bot).mp this

omit [CharP F p] in

theorem isSupersingular_iff_card_torsionBy_eq_one :
    IsSupersingular E p ↔ Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) = 1 := by
  rw [isSupersingular_iff_torsionBy_eq_bot]
  constructor
  · intro h; rw [h]; exact AddSubgroup.card_bot
  · intro h
    have := finite_torsionBy_natCast E hp.out.ne_zero
    exact (AddSubgroup.eq_bot_iff_card _).mpr h


omit [IsAlgClosed F] [E.IsElliptic] hp [CharP F p] in

theorem IsSupersingular.torsionBy_pow_eq_bot (h : IsSupersingular E p) (r : ℕ) :
    AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ) = ⊥ := by
  have key : ∀ (r : ℕ) (P : E.toAffine.Point), p ^ r • P = 0 → P = 0 := by
    intro r
    induction r with
    | zero => intro P hP; simpa using hP
    | succ r ih =>
      intro P hP
      exact h P (ih (p • P) (by rw [smul_smul, ← pow_succ]; exact hP))
  rw [eq_bot_iff]
  intro P hP
  exact (AddSubgroup.mem_bot).mpr (key r P ((mem_torsionBy_natCast_iff E _ P).mp hP))

noncomputable def torsionPowSucc (r : ℕ) :
    AddSubgroup.torsionBy E.toAffine.Point ((p ^ (r + 1) : ℕ) : ℤ) →+
      AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ) where
  toFun Q := ⟨p • Q.1, by
    rw [mem_torsionBy_natCast_iff, smul_smul, ← pow_succ]
    exact (mem_torsionBy_natCast_iff E _ _).mp Q.2⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [smul_add]

omit [CharP F p] in
theorem torsionPowSucc_surjective (r : ℕ) : Function.Surjective (torsionPowSucc E p r) := by
  intro R
  have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨Q, hQ⟩ := exists_zsmul_eq E hp0 R.1
  rw [natCast_zsmul] at hQ
  refine ⟨⟨Q, ?_⟩, Subtype.ext hQ⟩
  rw [mem_torsionBy_natCast_iff, pow_succ, ← smul_smul, hQ]
  exact (mem_torsionBy_natCast_iff E _ _).mp R.2

omit [IsAlgClosed F] [E.IsElliptic] hp [CharP F p] in
theorem card_ker_torsionPowSucc (r : ℕ) :
    Nat.card (torsionPowSucc E p r).ker = Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) := by
  refine Nat.card_congr
    { toFun := fun Q => ⟨Q.1.1, (mem_torsionBy_natCast_iff E p _).mpr
        (congrArg Subtype.val ((AddMonoidHom.mem_ker).mp Q.2))⟩
      invFun := fun P => ⟨⟨P.1, ?_⟩, ?_⟩
      left_inv := fun Q => rfl
      right_inv := fun P => rfl }
  · rw [mem_torsionBy_natCast_iff, pow_succ, ← smul_smul,
      (mem_torsionBy_natCast_iff E p _).mp P.2, smul_zero]
  · rw [AddMonoidHom.mem_ker]
    exact Subtype.ext ((mem_torsionBy_natCast_iff E p _).mp P.2)

omit [CharP F p] in

theorem card_torsionBy_pow_succ (r : ℕ) :
    Nat.card (AddSubgroup.torsionBy E.toAffine.Point ((p ^ (r + 1) : ℕ) : ℤ)) =
      Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) *
        Nat.card (AddSubgroup.torsionBy E.toAffine.Point ((p ^ r : ℕ) : ℤ)) := by
  have h := (torsionPowSucc E p r).ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr (torsionPowSucc_surjective E p r),
    AddSubgroup.card_top, card_ker_torsionPowSucc] at h
  exact h.symm


omit [CharP F p] in

theorem IsOrdinary.exists_addOrderOf_eq (h : IsOrdinary E p) (r : ℕ) :
    ∃ Q : E.toAffine.Point, p ^ r • Q = 0 ∧ addOrderOf Q = p ^ r := by
  cases r with
  | zero => exact ⟨0, smul_zero _, by rw [addOrderOf_zero, pow_zero]⟩
  | succ s =>
    have h' : ¬ IsSupersingular E p := h
    simp only [IsSupersingular, not_forall] at h'
    obtain ⟨P, hP, hP0⟩ := h'
    have hn : ((p ^ s : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero s hp.out.ne_zero
    obtain ⟨Q, hQ⟩ := exists_zsmul_eq E hn P
    rw [natCast_zsmul] at hQ
    have hfin : p ^ (s + 1) • Q = 0 := by rw [pow_succ', ← smul_smul, hQ, hP]
    exact ⟨Q, hfin, addOrderOf_eq_prime_pow (by rw [hQ]; exact hP0) hfin⟩



omit hp [CharP F p] in

theorem card_ker_mulIsogeny_natCast (hn : (p : ℤ) ≠ 0) :
    Nat.card (mulIsogeny E p hn).pointHom.ker =
      Nat.card (AddSubgroup.torsionBy E.toAffine.Point (p : ℤ)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun P => ?_)
  rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny,
    mem_torsionBy_natCast_iff, natCast_zsmul]

omit [CharP F p] in

theorem isSupersingular_iff_card_ker_mulIsogeny (hn : (p : ℤ) ≠ 0) :
    IsSupersingular E p ↔ Nat.card (mulIsogeny E p hn).pointHom.ker = 1 := by
  rw [card_ker_mulIsogeny_natCast, isSupersingular_iff_card_torsionBy_eq_one]

omit [CharP F p] in

private theorem finSepDegree_eq_card_ker' {E' : WeierstrassCurve F} [E'.IsElliptic]
    (φ : Isogeny E E') :
    Field.finSepDegree φ.comap.fieldRange E.toAffine.FunctionField = Nat.card φ.pointHom.ker := by
  have := φ.finiteDimensional
  have hmul := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic φ.comap.fieldRange φ.fixedKer
    E.toAffine.FunctionField
  rw [φ.finSepDegree_fixedKer, one_mul] at hmul
  exact le_antisymm φ.finSepDegree_le_card_ker (hmul ▸ φ.card_ker_le_finSepDegree_fixedKer)

omit [CharP F p] in

theorem isSupersingular_iff_isPurelyInseparable (hn : (p : ℤ) ≠ 0) :
    IsSupersingular E p ↔
      IsPurelyInseparable (mulIsogeny E p hn).comap.fieldRange E.toAffine.FunctionField := by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one, finSepDegree_eq_card_ker',
    isSupersingular_iff_card_ker_mulIsogeny]

omit [CharP F p] in

theorem isSupersingular_iff_insepDeg_mulIsogeny (hn : (p : ℤ) ≠ 0) :
    IsSupersingular E p ↔ (mulIsogeny E p hn).insepDeg = p ^ 2 := by
  have hd := (mulIsogeny E p hn).degree_eq_insepDeg_mul
  rw [degree_mulIsogeny, Int.natAbs_natCast] at hd
  rw [isSupersingular_iff_card_ker_mulIsogeny E p hn]
  have hp2 : 0 < p ^ 2 := pow_pos hp.out.pos 2
  constructor
  · intro h; rw [h, mul_one] at hd; exact hd.symm
  · intro h
    rw [h] at hd
    exact (Nat.mul_eq_left hp2.ne').mp hd.symm


end GroundTheory.Arith.Abelian
end

section
namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F] [DecidableEq F] (E E' : WeierstrassCurve F) (p : ℕ)
  [hp : Fact p.Prime] [CharP F p]

noncomputable def powFieldPoints :
    AddSubgroup (E'.baseChange E.toAffine.FunctionField).toAffine.Point :=
  (Point.map (W' := E') (powField E p).val).range

variable {E E'} [E.IsElliptic] [E'.IsElliptic]

omit [DecidableEq F] [E.IsElliptic] [E'.IsElliptic] in

theorem Isogeny.val_eq_some_x_y (φ : Isogeny E E') : φ.1 = Point.some φ.x φ.y φ.nonsingular := by
  obtain ⟨Q, ⟨x, y, h, rfl, -⟩, -⟩ := φ
  rfl

variable [IsAlgClosed F]

end GroundTheory.Arith.Abelian
end
