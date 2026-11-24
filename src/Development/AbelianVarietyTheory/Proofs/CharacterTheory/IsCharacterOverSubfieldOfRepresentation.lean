module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
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

open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

section
variable {K G V W : Type} [Field K] [Group G] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def transportRep (ρ : Representation K G V) (e : V ≃ₗ[K] W) : Representation K G W where
  toFun g := e.conj (ρ g)
  map_one' := by ext w; simp
  map_mul' a b := by ext w; simp

theorem transportRep_apply (ρ : Representation K G V) (e : V ≃ₗ[K] W) (g : G) (w : W) :
    transportRep ρ e g w = e (ρ g (e.symm w)) := rfl

theorem character_transportRep [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (e : V ≃ₗ[K] W) (g : G) :
    (transportRep ρ e).character g = ρ.character g :=
  LinearMap.trace_conj' (ρ g) e

def transportSubOrderIso (ρ : Representation K G V) (e : V ≃ₗ[K] W) :
    Subrepresentation (transportRep ρ e) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule.comap e.toLinearMap, fun g v hv => by
    have := S.apply_mem_toSubmodule g (v := e v) hv
    simpa [transportRep_apply] using this⟩
  invFun S := ⟨S.toSubmodule.comap e.symm.toLinearMap, fun g w hw => by
    have := S.apply_mem_toSubmodule g (v := e.symm w) hw
    simpa [transportRep_apply] using this⟩
  left_inv S := by ext w; simp
  right_inv S := by ext v; simp
  map_rel_iff' {S T} := by
    constructor
    · intro h w hw
      have h1 : e.symm w ∈ S.toSubmodule.comap e.toLinearMap := by
        show e (e.symm w) ∈ S.toSubmodule
        rw [e.apply_symm_apply]; exact hw
      have h2 : e (e.symm w) ∈ T.toSubmodule := h h1
      rw [e.apply_symm_apply] at h2
      exact h2
    · intro h v hv
      exact h (show e v ∈ S from hv)

end

theorem _root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (V : Type)
      [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K G V),
      _root_.GlobalTheory.BI.IsChar K L (fun g => algebraMap K L (ρ.character g)) ∧
        (ρ.IsIrreducible →
          _root_.GlobalTheory.BI.IsIrrChar K L (fun g => algebraMap K L (ρ.character g))) := by
  intro K L _ _ _ G _ V _ _ _ ρ
  set e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) := (Module.finBasis K V).equivFun
  have hchar : ∀ g, (_root_.GlobalTheory.BI.transportRep ρ e).character g = ρ.character g := by
    intro g
    exact LinearMap.trace_conj' (ρ g) e
  refine ⟨⟨Module.finrank K V, _root_.GlobalTheory.BI.transportRep ρ e, fun g => ?_⟩, fun hρ => ?_⟩
  · rw [hchar]
  · refine ⟨Module.finrank K V, _root_.GlobalTheory.BI.transportRep ρ e, ?_, fun g => ?_⟩
    · have hs : IsSimpleOrder (Subrepresentation ρ) := hρ
      exact (_root_.GlobalTheory.BI.transportSubOrderIso ρ e).isSimpleOrder_iff.mpr hs
    · rw [hchar]

end GlobalTheory.BI
