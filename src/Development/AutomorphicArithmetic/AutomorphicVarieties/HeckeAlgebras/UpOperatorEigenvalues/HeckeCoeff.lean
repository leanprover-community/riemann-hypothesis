module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.WdCharpoly
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HeckeMap

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Hi.Up

theorem hecke_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) :
    (heckePol n q a).map f = heckePol n q fun j => f (a j) :=
  _root_.UpperTheory.Reformulated.B.Qf17.hecke_map f n q a

private theorem hecke_coeff {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) (j : ℕ) (hj : j ≤ n) :
    (heckePol n q a).coeff (n - j) = (-1) ^ j * (q : A) ^ (j * (j - 1) / 2) * a j := by
  rw [heckePol, finsetSum_coeff, Finset.sum_eq_single j]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro i hi hij
    rw [coeff_C_mul_X_pow, if_neg]
    have := Finset.mem_range.1 hi
    omega
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

theorem hecke_cong {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (f : O →+* Qbar l) (ι : Qbar l ≃+* ℂ) {n q : ℕ}
    (hq : ‖(q : Qbar l)‖ = 1) (P : (Qbar l)[X]) (a : ℕ → ℂ) (b : ℕ → O) (hP : P.map ι.toRingHom = heckePol n q a)
    (h : ∀ k, ‖P.coeff k - ((heckePol n q b).map f).coeff k‖ < 1) (j : ℕ) (hj : j ≤ n) : ‖ι.symm (a j) - f (b j)‖ < 1 := by
  have e : P = heckePol n q fun j => ι.symm (a j) := by
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    rw [hP, hecke_map]
    simp
  have := h (n - j)
  rw [e, hecke_map, hecke_coeff _ _ _ _ hj, hecke_coeff _ _ _ _ hj, ← mul_sub] at this
  simpa [hq] using this

section Loc

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {w : Plc F} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}

theorem ord_uniq {hh : (F →+* Qbar l) → ℤ} {ω : (w.adicCompletion F)ˣ →* ℂˣ} {ψ ψ' : Dec (F := F) A →* (Qbar l)ˣ}
    (ho : OrdChar ι a ω hh ψ) (ho' : OrdChar ι a ω hh ψ') : ψ = ψ' := by
  have hd : DenseRange (Subgroup.inclusion (Weil_le_Dec h)) := UpperTheory.weil_group_dense_in_galois_group F Ω _ _ h
  refine MonoidHom.ext (congrFun (Continuous.ext_on hd ho.cont ho'.cont ?_))
  rintro _ ⟨s, rfl⟩
  exact Units.ext ((ho.val s _ rfl (Set.mem_univ _)).trans (ho'.val s _ rfl (Set.mem_univ _)).symm)

end Loc

section Set

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} {Q : QData V} {c : Coef l} {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r}
  {Λ : LamObj r} (R : HD Q ι Λ) (x : B.Pt) {lam : Wt L l n}

theorem under_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext z
  exact ((s.hw v) (algebraMap _ _ z)).symm.trans ((s.hA v) z)

end Set

end UpperTheory.V.Hi.Up
