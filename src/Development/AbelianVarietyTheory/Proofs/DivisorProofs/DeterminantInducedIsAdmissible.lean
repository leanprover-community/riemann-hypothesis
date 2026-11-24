module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.SmGL.ParIndAdm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_finset_KO_cover (K : Subgroup (GL n k)) (hK : IsOpen (K : Set (GL n k))) :
    ∃ R : Finset (GL n k), ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K := by
  obtain ⟨R, hR⟩ := (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := n)).elim_finite_subcover
    (fun x : GL n k => (fun y => x⁻¹ * y) ⁻¹' (K : Set (GL n k)))
    (fun x => hK.preimage (by fun_prop))
    (fun w _ => Set.mem_iUnion.2 ⟨w, by simp [one_mem]⟩)
  refine ⟨R, fun w hw => ?_⟩
  obtain ⟨r, hr, h⟩ := Set.mem_iUnion₂.1 (hR hw)
  exact ⟨r, hr, h⟩

theorem eq_zero_of_fixed (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) (K : Subgroup (GL n k))
    (R : Finset (GL n k)) (hR : ∀ w ∈ KO k n, ∃ r ∈ R, r⁻¹ * w ∈ K)
    (f : IndSp e ρ) (hf : f ∈ fixed (parInd e ρ) K) (h0 : ∀ r ∈ R, f.1.1 r = 0) : f = 0 := by
  have hfix : ∀ κ ∈ K, ∀ x, f.1.1 (x * κ) = f.1.1 x := fun κ hκ x => by
    have := congrArg (fun φ : IndSp e ρ => φ.1.1 x) (hf ⟨κ, hκ⟩)
    simpa using this
  apply Subtype.ext; apply Subtype.ext; funext x
  obtain ⟨u, l, w, hw, rfl⟩ := UnitInd.exists_iwasawa e x
  obtain ⟨r, hr, hrw⟩ := hR w hw
  let p : parab k e := ⟨(u : GL n k) * leviEmb k e l,
    mul_mem (unipRad_le_parab k e u.2) (leviEmb_mem_parab k e l)⟩
  have hw' : f.1.1 w = 0 := by
    have := hfix _ hrw r
    rw [mul_inv_cancel_left] at this
    rw [this, h0 r hr]
  show f.1.1 ((p : GL n k) * w) = 0
  rw [parInd_law, hw', map_zero, smul_zero]

theorem isAdmissible_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    [FiniteDimensional ℂ W] : IsAdmissible (parInd e ρ) := by
  refine ⟨isSmooth_parInd e ρ, fun K hKo _ => ?_⟩
  obtain ⟨R, hR⟩ := exists_finset_KO_cover K hKo
  let L : fixed (parInd e ρ) K →ₗ[ℂ] (R → W) :=
    { toFun := fun f r => f.1.1.1 r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective L fun f g hfg => ?_
  rw [← sub_eq_zero]
  have h := eq_zero_of_fixed e ρ K R hR (f - g).1 (f - g).2 fun r hr => by
    have := congrFun hfg ⟨r, hr⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this
    show f.1.1.1 r - g.1.1.1 r = 0
    rw [this, sub_self]
  exact Subtype.ext h

end GlobalTheory.SmGL.ParIndAdm

namespace GlobalTheory.ThK.MidJac

end GlobalTheory.ThK.MidJac
