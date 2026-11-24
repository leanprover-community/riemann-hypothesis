module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PtrScalar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Helpers
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tpsc_single_mem {S : Submodule ℂ M} {x : M} (hx : x ∈ S) (c : Fin n) :
    (Pi.single c x : Fin n → M) ∈ tensSub S := by
  refine Submodule.mem_pi.2 fun d _ => ?_
  by_cases h : d = c
  · subst h; simpa using hx
  · simp [h]

theorem tpsc_coord_mem {S : Submodule ℂ M} {f : Fin n → M} (hf : f ∈ tensSub S) (c : Fin n) : f c ∈ S :=
  Submodule.mem_pi.1 hf c (Set.mem_univ _)

theorem tpsc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensV E a b (Pi.single c x) = Pi.single c (E a b x) + if b = c then Pi.single a x else 0 := by
  funext d
  rw [tensV_coord]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
    simp [Pi.single_apply, hdc, hda, hbc] <;> split_ifs <;> simp_all

theorem tpsc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensVd E a b (Pi.single c x) = Pi.single c (E a b x) - if a = c then Pi.single b x else 0 := by
  funext d
  rw [tensVd_coord]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>
    simp [Pi.single_apply, hdc, hdb, hac] <;> split_ifs <;> simp_all

end Helpers

def tpscK (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ := cond dual (star (k c d)) (k c d)

theorem tpscK_rows {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (c c' : Fin n) : ∑ d, tpscK dual k c' d * star (tpscK dual k c d) = if c' = c then 1 else 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.tpscK_rows <;> assumption

theorem tpscK_cols {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (e d : Fin n) : ∑ c, tpscK dual k c d * star (tpscK dual k c e) = if e = d then 1 else 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.tpscK_cols <;> assumption

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D} {A : Module.End ℂ (Fin n → D)}

theorem ptr_mem {dual : Bool} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ x ∈ genSub E V, ptr A x ∈ genSub E V := by
  intro x hx
  rw [ptr_apply]
  exact Submodule.sum_mem _ fun c _ => tpsc_coord_mem (hA.1 _ (tpsc_single_mem hx c)) c

theorem ptr_comm {dual : Bool} (hE : IsGlRep E) (hA : IsGKEndo dual ε σ E (genSub E V) A) (a b : Fin n) :
    ∀ x ∈ genSub E V, ptr A (E a b x) = E a b (ptr A x) := by
  apply ReciprocityTheory.ChartRestriction.DS.ptr_comm <;> assumption

theorem tpsc_kDiag (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) (c : Fin n) :
    kDiag dual σ k f c = ∑ d, tpscK dual k c d • σ k (f d) := rfl

theorem ptr_kcomm {dual : Bool} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, (y : H) = σ k (x : H) →
      ((ptr A y : D) : H) = σ k ((ptr A x : D) : H) := by
  apply ReciprocityTheory.ChartRestriction.DS.ptr_kcomm <;> assumption

end

theorem ptr_scalar (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∃ c : ℂ, ∀ x ∈ genSub E V, ptr A x = c • x :=
  data_end_scalar hgap hσ hD hV hc hVK (ptr A) (ptr_mem hA) (fun a b => ptr_comm hD.glRep hA a b)
    (ptr_kcomm hσ hD hA)

end ReciprocityTheory.ChartRestriction.DS.G2
