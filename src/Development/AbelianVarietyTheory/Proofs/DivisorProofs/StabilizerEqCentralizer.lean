module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.GroupAction.Basic

@[expose] public section

noncomputable section

namespace GlobalTheory.OrbitUnfold

def ConjSelf (Γ : Type) : Type := Γ

namespace ConjSelf

variable {Γ : Type} [Group Γ]

def of (γ : Γ) : ConjSelf Γ := γ

def val (γ : ConjSelf Γ) : Γ := γ

instance : MulAction Γ (ConjSelf Γ) where
  smul η γ := of (η * val γ * η⁻¹)
  one_smul γ := by
    change (1 : Γ) * val γ * 1⁻¹ = val γ
    simp
  mul_smul a b γ := by
    change a * b * val γ * (a * b)⁻¹ = a * (b * val γ * b⁻¹) * a⁻¹
    group

theorem val_smul (η : Γ) (γ : ConjSelf Γ) : val (η • γ) = η * val γ * η⁻¹ := rfl

theorem stabilizer_eq_centralizer (γ : ConjSelf Γ) :
    MulAction.stabilizer Γ γ = Subgroup.centralizer {val γ} := by
  ext η
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg val h
    rw [val_smul] at h'
    calc η * val γ = η * val γ * η⁻¹ * η := by group
      _ = val γ * η := by rw [h']
  · intro h
    change η * val γ * η⁻¹ = val γ
    rw [h.eq]
    group

end ConjSelf

open ConjSelf

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

theorem stabilizer_pair (p : Y × ConjSelf Γ) :
    MulAction.stabilizer Γ p = MulAction.stabilizer Γ p.1 ⊓ Subgroup.centralizer {val p.2} := by
  rw [← stabilizer_eq_centralizer]
  ext η
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Prod.smul_def, Prod.ext_iff]

def pairTerm (F : Y → Γ → ℂ) (p : Y × ConjSelf Γ) : ℂ :=
  ((Nat.card (MulAction.stabilizer Γ p) : ℕ) : ℂ)⁻¹ * F p.1 (val p.2)

theorem pairTerm_smul (F : Y → Γ → ℂ) (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (η : Γ) (p : Y × ConjSelf Γ) : pairTerm F (η • p) = pairTerm F p := by
  unfold pairTerm
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.card_map_of_injective (MulAut.conj η).injective]
  congr 1
  exact hF η p.1 (val p.2)

theorem pairTerm_out (F : Y → Γ → ℂ) (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (p : Y × ConjSelf Γ) :
    pairTerm F (Quotient.out (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p)) = pairTerm F p := by
  obtain ⟨η, hη⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ (Y × ConjSelf Γ)) p))
  rw [← hη]
  exact pairTerm_smul F hF η p

def pairSum (F : Y → Γ → ℂ) : ℂ :=
  ∑ᶠ o : MulAction.orbitRel.Quotient Γ (Y × ConjSelf Γ), pairTerm F (Quotient.out o)

end GlobalTheory.OrbitUnfold
