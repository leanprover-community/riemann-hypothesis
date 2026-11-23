module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem seamEx_lin_cpt {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] E) (x : Fin n → K) :
    lin (fun k => j (Pi.single k 1)) (cpt σ x) = j x := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]

  simp only [lin, cpt, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ]

theorem seamEx_coords {K V E ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {n : ℕ} (j : V →ₛₗ[σ] E) (b : Module.Basis ι K V) (e : (Fin n → K) ≃ₗ[K] V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (b i))) = ⊤) :
    ∃ c : E ≃ₗ[ℂ] (Fin n → ℂ), ∀ x, c.symm (cpt σ x) = j (e x) := by
  let g : (Fin n → K) →ₛₗ[σ] E := j.comp e.toLinearMap
  let f : (Fin n → ℂ) →ₗ[ℂ] E := lin (fun k => g (Pi.single k 1))
  have hf : ∀ x, f (cpt σ x) = j (e x) := fun x => seamEx_lin_cpt σ g x
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cpt σ (e.symm (b i)), by rw [hf]; simp⟩
  haveI : Module.Finite K V := Module.Finite.equiv e
  haveI : Finite ι := Module.Finite.finite_basis b
  haveI : Fintype ι := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ E := Module.Basis.mk hb.1 hb.2.ge
  haveI : Module.Finite ℂ E := Module.Finite.of_basis B
  have hr : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ E := by
    rw [Module.finrank_eq_card_basis B, ← Module.finrank_eq_card_basis b, ← e.finrank_eq]
    simp
  have hinj : Function.Injective f := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).2 hsurj
  exact ⟨(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm, hf⟩

theorem seam_nonempty (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs)
    (s : Bool) (R : Read D X fc s) (cr : Crd A fc) : Nonempty (Seam R cr) := by
  choose cφ hφ using fun u => seamEx_coords D.what₂.embLL (D.jN u) (D.div.Nu u).b (R.eNu u) (D.jN_basis u)
  obtain ⟨c, hc⟩ := seamEx_coords D.what₂.embLL D.jEE D.div.RR.b R.eRR D.jEE_basis
  refine ⟨{ cφ := cφ
            cF := lin (fun k => R.jV (Pi.single k 1))
            eR :=
              { toFun := fun F => X.iC cr true Bs.μ0 (cjv s (c F))
                map_add' := fun F G => ?_
                map_smul' := fun a F => ?_ }
            cφ_eq := hφ
            cF_eq := fun y => seamEx_lin_cpt _ _ y
            eR_eq := fun y => ?_ }⟩
  · rw [← map_add (f := _)]
    congr 1
    funext i
    simp [cjv]
  · rw [← map_smul]
    congr 1
    funext i
    simp [cjv]
  · show X.iC cr true Bs.μ0 (cjv s (c _)) = _
    rw [← hc, LinearEquiv.apply_symm_apply]
    congr 1
    funext i
    simp [cjv, cpt, R.twist]

end GlobalTheory.Mem.SJ

end
