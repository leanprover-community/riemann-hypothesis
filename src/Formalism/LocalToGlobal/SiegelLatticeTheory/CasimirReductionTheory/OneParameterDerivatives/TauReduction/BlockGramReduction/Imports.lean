module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.FiniteAbelian.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.Tau

theorem t2 : ExistsBoundedBasis := by
  intro K _ _ n j M B b hM hBM hli hbB hBspan
  classical
  have hBfg : B.FG := by
    haveI := isNoetherian_of_fg_of_noetherian M hM
    have h1 : (B.comap M.subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map M.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hBM] at h2
  obtain ⟨s, hs⟩ := hBfg
  have hcoef : ∀ g ∈ s, ∃ c : Fin j → K, ∑ a, c a • b a = g := fun g hg =>
    (Submodule.mem_span_range_iff_exists_fun K).mp (hBspan (hs ▸ Submodule.subset_span hg))
  choose! c hc using hcoef
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((s ×ˢ Finset.univ).image (fun p : (Fin n → K) × Fin j => c p.1 p.2))
  have hyg : ∀ g ∈ s, (y : ℤ) • g ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro g hg
    rw [← hc g hg, Finset.smul_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    have hint : IsIntegral ℤ (y • c g a) :=
      hy _ (Finset.mem_image.mpr ⟨(g, a), Finset.mem_product.mpr ⟨hg, Finset.mem_univ a⟩, rfl⟩)
    have e : (y : ℤ) • (c g a • b a) = (⟨y • c g a, hint⟩ : 𝓞 K) • b a := by
      rw [← smul_assoc]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hyB : ∀ v ∈ B, (y : ℤ) • v ∈ Submodule.span (𝓞 K) (Set.range b) := by
    rw [← hs]
    intro v hv
    refine Submodule.span_induction (fun g hg => hyg g hg) (by simp)
      (fun u w _ _ hu hw => by rw [smul_add]; exact add_mem hu hw)
      (fun o u _ hu => by rw [smul_comm]; exact Submodule.smul_mem _ o hu) hv
  haveI : Module.Finite (𝓞 K) B := Module.Finite.iff_fg.mpr ⟨s, hs⟩
  haveI : Module.Finite ℤ (B ⧸ (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) :=
    Module.Finite.trans (𝓞 K) _
  apply Module.finite_of_fg_torsion
  intro q
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) q
  refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
  show (y : ℤ) • (Submodule.Quotient.mk (p := (Submodule.span (𝓞 K) (Set.range b)).comap B.subtype) v) = 0
  have hz := map_zsmul (Submodule.mkQ ((Submodule.span (𝓞 K) (Set.range b)).comap B.subtype)) y v
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at hz
  rw [← hz, Submodule.Quotient.mk_eq_zero]
  exact hyB v v.2

end Formalism.L2.SG.Pf.Tau
