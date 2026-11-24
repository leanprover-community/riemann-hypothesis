module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroBasicTwistOfSpecialForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spOrd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_one (n : ℕ) : ∑ _a : Fin n, (1 : ℕ) = n := by simp

theorem stdBlocks_one (n : ℕ) :
    (stdBlocks (fun _ : Fin n => 1) (sum_one n) : (Σ _ : Fin n, Fin 1) ≃ Fin n) =
      Equiv.sigmaUnique (Fin n) (fun _ => Fin 1) := by
  refine Equiv.ext fun x => ?_
  obtain ⟨a, i⟩ := x
  refine Fin.ext ?_
  rw [stdBlocks_val]
  simp

theorem isSmooth_detRep1 {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : IsSmooth (detRep (Fin 1) χ) :=
  (isSmooth_ofChar_iff _).2 (h.detChar (n := Fin 1))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hasFiniteLength_detRep1 (χ : kˣ →* ℂˣ) : HasFiniteLength (detRep (R := k) (Fin 1) χ) :=
  hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _)

theorem prin_sub_multi {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) :
    IsSubquotient (prinSeries χ)
      (multiProd (stdBlocks (fun _ : Fin n => 1) (sum_one n)) fun i => detRep (Fin 1) (χ i)) := by
  have h := GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ
  rw [← stdBlocks_one] at h
  exact h

end UpperTheory.TNZ.Grp.P_spOrd

namespace UpperTheory.TNZ.Grp

open UpperTheory.TNZ.Grp.P_spOrd GlobalTheory.LocGL.SupportRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem step_spOrd : SpecialOrderProp (k := k) (n := n) := by
  intro hL V _ _ π hs hi c hc σ h
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hL.loc.zel k
  obtain ⟨hp1, e1⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c (σ i))) (fun i => isSmooth_detRep1 (hc (σ i)))
    (fun i => hasFiniteLength_detRep1 (c (σ i)))
  obtain ⟨hp2, e2⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c i)) (fun i => isSmooth_detRep1 (hc i))
    (fun i => hasFiniteLength_detRep1 (c i))
  have hcl : clsGL _ hp1 = clsGL _ hp2 := by
    apply Ψ.injective
    rw [e1, e2]
    exact Equiv.prod_comp σ (fun i => Ψ (clsGL (detRep (Fin 1) (c i)) (hasFiniteLength_detRep1 (c i))))
  have h1 := h.trans (prin_sub_multi (fun i => c (σ i)))
  have h2 := clsGL_of_pos hp1 hs hi h1
  rw [hcl] at h2
  exact (isSubquotient_of_clsGL_ne hp2 hs hi h2.ne').trans
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries _ c)

end UpperTheory.TNZ.Grp
