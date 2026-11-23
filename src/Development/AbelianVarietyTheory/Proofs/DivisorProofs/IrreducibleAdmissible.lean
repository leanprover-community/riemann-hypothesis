module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.BZBridge

section Transport

variable {H G V : Type} [Group H] [Group G] [TopologicalSpace H] [TopologicalSpace G]
  [AddCommGroup V] [Module ℂ V]

def subrepCompEquiv (π : Representation ℂ G V) (Φ : H ≃* G) :
    Subrepresentation (π.comp Φ.toMonoidHom : Representation ℂ H V) ≃o Subrepresentation π where
  toFun U := ⟨U.toSubmodule, fun g v hv => by
    have h := U.apply_mem_toSubmodule (Φ.symm g) hv
    simpa using h⟩
  invFun U := ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (Φ g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp (π : Representation ℂ G V) (Φ : H ≃* G) (h : π.IsIrreducible) :
    Representation.IsIrreducible (π.comp Φ.toMonoidHom : Representation ℂ H V) := by
  have := h
  exact (subrepCompEquiv π Φ).isSimpleOrder

theorem isSmooth_comp (π : Representation ℂ G V) (Φ : H ≃ₜ* G) (h : IsSmooth π) :
    IsSmooth (π.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H V) := by
  intro v
  exact (h v).preimage (map_continuous Φ)

theorem isAdmissible_of_comp (π : Representation ℂ G V) (Φ : H ≃ₜ* G) (hs : IsSmooth π)
    (h : IsAdmissible (π.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ H V)) : IsAdmissible π := by
  refine ⟨hs, fun K hKo hKc => ?_⟩

  set K' : Subgroup H := K.comap Φ.toMulEquiv.toMonoidHom with hK'
  have hset : (K' : Set H) = Φ.symm '' (K : Set G) := by
    ext x
    constructor
    · intro hx
      exact ⟨Φ x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      show Φ (Φ.symm y) ∈ K
      simpa using hy
  have hK'o : IsOpen (K' : Set H) := hKo.preimage (map_continuous Φ)
  have hK'c : IsCompact (K' : Set H) := by
    rw [hset]
    exact hKc.image (map_continuous Φ.symm)
  have := h.2 K' hK'o hK'c
  refine Submodule.finiteDimensional_of_le (S₂ := fixed (π.comp Φ.toMulEquiv.toMonoidHom) K') ?_
  intro v hv
  simp only [fixed, eig, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq] at hv ⊢
  intro x
  have h1 := hv ⟨Φ x, x.2⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
  exact h1

end Transport

def glReindex (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ε : ι ≃ κ) : GL ι K ≃ₜ* GL κ K where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv K K ε).toMulEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩

theorem irreducibleAdmissible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : IrreducibleAdmissible k := by
  intro n _ _ V _ _ π hs hi
  let Φ := glReindex k (Fintype.equivFin n).symm
  exact isAdmissible_of_comp π Φ hs
    (hA k (Fintype.card n) V _ (isSmooth_comp π Φ hs) (isIrreducible_comp π Φ.toMulEquiv hi))

end GlobalTheory.BZBridge
