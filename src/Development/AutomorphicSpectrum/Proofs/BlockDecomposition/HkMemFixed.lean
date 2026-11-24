module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeFix

theorem hk_mem_fixed : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e : GL ι F → ℂ), IsHk K e → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V), ∀ v ∈ fixed ρ K, hk ρ K e v ∈ fixed ρ K ∧ ∀ g : GL ι F, (∀ q : GL ι F ⧸ K, e (g * q.out) = e q.out) → True := by
  intro F _ _ _ _ ι _ _ K e hE V _ _ ρ v hv
  refine ⟨?_, fun _ _ => trivial⟩
  have hfix : ∀ c ∈ K, ρ c v = v := by
    intro c hc
    have := hv ⟨c, hc⟩
    simpa using this
  have hbi := hE.2.2.2
  intro h
  have hk' : (h : GL ι F) ∈ K := h.2
  set k : GL ι F := (h : GL ι F) with hkdef
  have hinj : Function.Injective (ρ k : V →ₗ[ℂ] V) := by
    intro x y hxy
    have h1 : ∀ z, ρ k⁻¹ (ρ k z) = z := by
      intro z
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← h1 x, ← h1 y, hxy]
  have hstep : ∀ q : GL ι F ⧸ K, ρ k (e q.out • ρ q.out v) =
      e (k • q).out • ρ (k • q).out v := by
    intro q
    have hq : k • q = QuotientGroup.mk (k * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (k * q.out)
    rw [hq, hc, hbi k hk' c c.2 q.out, map_smul, map_mul, Module.End.mul_apply, map_mul,
      Module.End.mul_apply, hfix c c.2]
  have hsum : ρ k (hk ρ K e v) = hk ρ K e v := by
    unfold hk
    have h1 := AddMonoidHom.map_finsum_of_injective (ρ k : V →ₗ[ℂ] V).toAddMonoidHom hinj
      (fun q : GL ι F ⧸ K => e q.out • ρ q.out v)
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    rw [h1]
    simp only [hstep]
    exact finsum_comp_equiv (f := fun q : GL ι F ⧸ K => e q.out • ρ q.out v) (MulAction.toPerm k)
  simpa using hsum

end GlobalTheory.CompanionTheory.HeckeFix
