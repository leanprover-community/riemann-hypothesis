module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccDAdjA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
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
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefBTensSubKStable
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem adjA_rep (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {lam : Fin n → ℝ} {V V' : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hV'f : FiniteDimensional ℂ V')
    (hV'k : IsKStableSub ε E V') {ps : (Fin n → D) →ₗ[ℂ] D}
    (hps : ∀ a b, ∀ f ∈ tensSub (genSub E V), ps (tensF dual E a b f) = E a b (ps f))
    {x' : D} (hx' : x' ∈ genSub E V') (c : Fin n) :
    ∃ z ∈ genSub E V, ∀ y ∈ genSub E V, inner ℂ z y = inner ℂ x' (ps (Pi.single c y)) := by
  classical
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hUk := isKUnitary_of_isInfUnitary hU
  obtain ⟨m', hm'⟩ := exists_layer_of_mem_genSub hE hV'k hx'
  set L' := layer ε E V' m'
  have hL'f : FiniteDimensional ℂ L' := finiteDimensional_layer hV'f m'
  have hL'k : IsKStableSub ε E L' := layer_kStable hE hV'k m'
  set bs := Module.finBasis ℂ L'
  set Φ : D →ₗ[ℂ] (Fin n × Fin (Module.finrank ℂ L') → ℂ) :=
    LinearMap.pi fun p => (innerₛₗ ℂ (bs p.2 : D)).comp (ps.comp (LinearMap.single ℂ (fun _ => D) p.1))
  have hΦ : ∀ y, ∀ p : Fin n × Fin (Module.finrank ℂ L'), Φ y p = inner ℂ (bs p.2 : D) (ps (Pi.single p.1 y)) :=
    fun y p => rfl

  set P : D → Prop := fun y => ∀ v ∈ L', ∀ c, inner ℂ v (ps (Pi.single c y)) = 0
  have hPΦ : ∀ y, Φ y = 0 → P y := by
    intro y hy v hv c
    have hv' : v = ∑ i, (bs.repr ⟨v, hv⟩ i) • (bs i : D) := by
      have := congrArg Subtype.val (bs.sum_repr ⟨v, hv⟩)
      rw [Submodule.coe_sum] at this
      simpa only [Submodule.coe_smul] using this.symm
    rw [hv', sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_left, ← hΦ y (c, i), hy, Pi.zero_apply, mul_zero]
  have hΦP : ∀ y, P y → Φ y = 0 := by
    intro y hy
    funext p
    rw [hΦ, Pi.zero_apply]
    exact hy _ (bs p.2).2 p.1
  have hMk : IsKStableSub ε E (genSub E V) := fun a b _ v hv => closure_E_mem_genSub a b hv
  have hPE : ∀ y ∈ genSub E V, P y → ∀ a b, ε a = ε b → P (E a b y) := by
    intro y hy hPy a b hab v hv c
    obtain ⟨c', r, hcr⟩ := adjA_tensF_single dual E a b c y
    have h1 : ps (Pi.single c (E a b y)) = E a b (ps (Pi.single c y)) - r • ps (Pi.single c' y) := by
      rw [← hps a b _ (adjA_single_mem c hy), hcr, map_add (f := _), map_smul]
      abel
    rw [h1, inner_sub_right, inner_smul_right, hPy v hv c', mul_zero, sub_zero, ← hUk b a hab.symm]
    exact hPy _ (hL'k b a hab.symm v hv) c
  have hPadd : ∀ s : Finset (Fin n), ∀ g : Fin n → D, (∀ q ∈ s, P (g q)) → P (∑ q ∈ s, g q) := by
    intro s g hg v hv c
    have : (Pi.single c (∑ q ∈ s, g q) : Fin n → D) = ∑ q ∈ s, Pi.single c (g q) := by
      funext x
      simp only [Pi.single_apply, Finset.sum_apply]
      split_ifs <;> simp

    rw [this, map_sum, inner_sum]
    exact Finset.sum_eq_zero fun q hq => hg q hq v hv c
  have hcasP : ∀ y ∈ genSub E V, P y → P (casimirK ε E y) := by
    intro y hy hPy
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
    refine hPadd _ _ fun a _ => hPadd _ _ fun b hb => ?_
    have hq' : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hPE _ (closure_E_mem_genSub _ _ hy) (hPE y hy hPy b a hq') a b hq'.symm
  obtain ⟨C, hC⟩ := adjA_high (genSub E V) (casimirK ε E)
    (fun y hy => casimirK_mem_of_kStable hMk hy) Φ (fun y hy h0 => hΦP _ (hcasP y hy (hPΦ y h0)))
  obtain ⟨K, hK⟩ := coefB_adm hE hU hV hc hgap C
  have hTsym : ∀ x y, inner ℂ (casimirK ε E x) y = inner ℂ x (casimirK ε E y) := casimirK_inner_symm hUk
  set ℓ : D →ₗ[ℂ] ℂ := (innerₛₗ ℂ x').comp (ps.comp (LinearMap.single ℂ (fun _ => D) c))
  obtain ⟨z, hzM, hz⟩ := coefA_toSum hTsym (coefB_locFin hE hV.1 hV.2.1) ℓ C
    (finiteDimensional_layer hV.1 K) (layer_le_genSub K) (fun y hy θ hθ hyθ => hK y hy θ hθ hyθ)
    (fun y hy θ hθ hyθ => hPΦ y (hC y hy θ hθ hyθ) x' hm' c)
  exact ⟨z, hzM, fun y hy => hz y hy⟩

end Rep

end ReciprocityTheory.ChartRestriction.DS.G2
