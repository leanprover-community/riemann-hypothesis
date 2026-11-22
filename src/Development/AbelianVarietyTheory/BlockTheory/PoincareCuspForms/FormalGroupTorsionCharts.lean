module

public import Mathlib
public import ReciprocityTheory.DualLattices.HtLinStatement

@[expose] public section

noncomputable section

open IsLocalRing TensorProduct ReciprocityTheory.PGsh

namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts

universe u v

section Eval

variable {A : Type*} {R : Type*} [CommRing A] [CommRing R] [Algebra A R] {σ : Type*}

def evalTerm (F : MvPowerSeries σ A) (x : σ → R) (d : σ →₀ ℕ) : R :=
  MvPowerSeries.coeff d F • d.prod fun i n => x i ^ n

theorem evalTerm_finite [Finite σ] (F : MvPowerSeries σ A) (x : σ → R)
    (hx : ∀ i, IsNilpotent (x i)) : (Function.support (evalTerm F x)).Finite := by
  classical
  choose N hN using hx
  haveI := Fintype.ofFinite σ
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm N)).subset fun d hd => ?_
  by_contra hcon
  apply hd
  have : ∃ i, N i < d i := by
    by_contra h
    push Not at h
    exact hcon fun i => by simpa using h i
  obtain ⟨i, hi⟩ := this
  have hi0 : i ∈ d.support := by
    rw [Finsupp.mem_support_iff]; omega
  unfold evalTerm
  have h0 : x i ^ d i = 0 := pow_eq_zero_of_le hi.le (hN i)
  rw [Finsupp.prod, Finset.prod_eq_zero (f := fun a => x a ^ d a) hi0 h0, smul_zero]

end Eval

variable {R₀ : Type u} [CommRing R₀]

variable {k : LAlg R₀}

namespace TorsionRep

variable {B : BX R₀} {p : ℕ} {O : ResAlg k} (D : TorsionRep B p O)

variable (C : Type v) [Field C] [Algebra (O.alg : Type u) C]

end TorsionRep

end GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
