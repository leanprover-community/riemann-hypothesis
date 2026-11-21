import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.Struct
import Mathlib

section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

section Int

variable {σ τ Kc : Type} [Field Kc] (Oc : Subring Kc)

def IntP (x : MvPolynomial τ Kc) : Prop := ∀ m, MvPolynomial.coeff m x ∈ Oc

theorem coeffsIn_zero : IntP Oc (0 : MvPolynomial τ Kc) := fun m => by simp [Oc.zero_mem]

theorem coeffsIn_one : IntP Oc (1 : MvPolynomial τ Kc) := fun m => by
  classical
  rw [MvPolynomial.coeff_one]; split_ifs
  · exact Oc.one_mem
  · exact Oc.zero_mem

theorem coeffsIn_add {x y : MvPolynomial τ Kc} (hx : IntP Oc x) (hy : IntP Oc y) : IntP Oc (x + y) := fun m => by
  rw [MvPolynomial.coeff_add]; exact Oc.add_mem (hx m) (hy m)

theorem coeffsIn_mul₂ {x y : MvPolynomial τ Kc} (hx : IntP Oc x) (hy : IntP Oc y) : IntP Oc (x * y) := fun m => by
  classical
  rw [MvPolynomial.coeff_mul]
  exact Oc.sum_mem fun q _ => Oc.mul_mem (hx _) (hy _)

theorem coeffsIn_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial τ Kc) (h : ∀ i ∈ s, IntP Oc (f i)) :
    IntP Oc (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntP Oc) (fun _ _ => coeffsIn_add Oc) (coeffsIn_zero Oc) h

theorem IntA_zero : IntA Oc (0 : MvPowerSeries σ (MvPolynomial τ Kc)) := fun n => by
  simp only [map_zero]; exact coeffsIn_zero Oc

theorem IntA_one : IntA Oc (1 : MvPowerSeries σ (MvPolynomial τ Kc)) := fun n => by
  classical
  rw [MvPowerSeries.coeff_one]; split_ifs
  · exact coeffsIn_one Oc
  · exact coeffsIn_zero Oc

theorem IntA_add {F G : MvPowerSeries σ (MvPolynomial τ Kc)} (hF : IntA Oc F) (hG : IntA Oc G) :
    IntA Oc (F + G) := fun n => by
  rw [map_add]; exact coeffsIn_add Oc (hF n) (hG n)

theorem IntA_mul {F G : MvPowerSeries σ (MvPolynomial τ Kc)} (hF : IntA Oc F) (hG : IntA Oc G) :
    IntA Oc (F * G) := fun n => by
  classical
  rw [MvPowerSeries.coeff_mul]
  exact coeffsIn_sum Oc _ _ fun q _ => coeffsIn_mul₂ Oc (hF _) (hG _)

end Int

end PI.UnitaryGroupMassFormula.PadicGainBound
end
end

section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

section Agree

variable {σ A : Type} [CommRing A]

def Agree (D : ℕ) (F G : MvPowerSeries σ A) : Prop :=
  ∀ n : σ →₀ ℕ, n.degree ≤ D → MvPowerSeries.coeff n F = MvPowerSeries.coeff n G

end Agree

section Gen

variable {σ τ ι Kc : Type} [Field Kc] (p : ℕ) (Oc : Subring Kc) (T : ι → MvPowerSeries σ (MvPolynomial τ Kc))

end Gen

end PI.UnitaryGroupMassFormula.PadicGainBound
end
end

section
namespace PI.PadicCongruence

variable {R : Type*} [CommRing R] (S : Subring R) (p : ℕ)

def ModP (x y : R) : Prop := ∃ z ∈ S, x = y + (p : R) * z

theorem ModP.trans {x y w : R} (h1 : ModP S p x y) (h2 : ModP S p y w) : ModP S p x w := by
  obtain ⟨z1, hz1, rfl⟩ := h1
  obtain ⟨z2, hz2, rfl⟩ := h2
  exact ⟨z2 + z1, S.add_mem hz2 hz1, by ring⟩

theorem ModP.add {x y x' y' : R} (h : ModP S p x y) (h' : ModP S p x' y') : ModP S p (x + x') (y + y') := by
  obtain ⟨z, hz, rfl⟩ := h
  obtain ⟨z', hz', rfl⟩ := h'
  exact ⟨z + z', S.add_mem hz hz', by ring⟩

end PI.PadicCongruence
end

section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

section Sub

variable {σ τ Kc : Type} [Field Kc] (Oc : Subring Kc)

def intSub : Subring (MvPowerSeries σ (MvPolynomial τ Kc)) where
  carrier := {F | IntA Oc F}
  mul_mem' := IntA_mul Oc
  one_mem' := IntA_one Oc
  add_mem' := IntA_add Oc
  zero_mem' := IntA_zero Oc
  neg_mem' := fun hF n m => by
    rw [map_neg, MvPolynomial.coeff_neg]; exact Oc.neg_mem (hF n m)

end Sub

section Low

variable {σ A : Type} [CommRing A]

def LowOrd (k : ℕ) (F : MvPowerSeries σ A) : Prop :=
  ∀ e : σ →₀ ℕ, e.degree < k → MvPowerSeries.coeff e F = 0

end Low

section Trunc

variable (Sh : Shape) {Kc : Type} [Field Kc]

end Trunc

section Trunc2

variable (Sh : Shape) {Kc : Type} [Field Kc]

def sT (p : ℕ) (v : Fin Sh.nV) (e : Fin (Sh.n' v)) (a : Fin Sh.r0) (b : Fin Sh.r1) (D : ℕ) : MvPowerSeries Sh.ZV Kc :=
  ∑ l ∈ range (D + 1), MvPowerSeries.C ((-1 : Kc) ^ l) *
    MvPowerSeries.X (⟨v, (FormalGroupSystem.posSub e (2 * l), a, b)⟩ : Sh.ZV) ^ (p ^ (2 * l))

def sig (p : ℕ) (TT : ∀ v, Finset (Fin (Sh.n' v))) (v : Fin Sh.nV) (e : Fin (Sh.n' v)) (a : Fin Sh.r0) (b : Fin Sh.r1)
    (D : ℕ) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  ∑ l ∈ range (D + 1), MvPowerSeries.C (MvPolynomial.C ((-1 : Kc) ^ l)) *
    subV Sh Kc TT ⟨v, (FormalGroupSystem.posSub e (2 * l), a, b)⟩ ^ (p ^ (2 * l))

end Trunc2

section AgreeSum

variable {σ A : Type} [CommRing A]

theorem Agree.add {D : ℕ} {F F' G G' : MvPowerSeries σ A} (hF : Agree D F F') (hG : Agree D G G') :
    Agree D (F + G) (F' + G') := fun n hn => by rw [map_add, map_add, hF n hn, hG n hn]

end AgreeSum

end PI.UnitaryGroupMassFormula.PadicGainBound
end
end

section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset PI.PadicCongruence
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

section Cong

variable (Sh : Shape) {Kc : Type} [Field Kc] (Oc : Subring Kc)

def Wt (p : ℕ) (TT : ∀ v, Finset (Fin (Sh.n' v))) (v : Fin Sh.nV) (e : Fin (Sh.n' v)) (a : Fin Sh.r0) (b : Fin Sh.r1)
    (D : ℕ) (j : ℕ → ℕ) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  ∑ l ∈ range (D + 1), MvPowerSeries.C (MvPolynomial.C ((-1 : Kc) ^ l)) *
    (zt p Sh Kc v (FormalGroupSystem.posSub e (2 * l)) (j l) a b + ut p Sh Kc TT v (FormalGroupSystem.posSub e (2 * l)) (j l) a b)

end Cong

section Expand

variable (Sh : Shape) {Kc : Type} [Field Kc]

end Expand

end PI.UnitaryGroupMassFormula.PadicGainBound
end
end
