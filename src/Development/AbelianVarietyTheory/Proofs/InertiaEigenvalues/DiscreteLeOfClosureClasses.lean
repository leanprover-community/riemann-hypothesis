module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLinearCombination
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
  GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

namespace GlobalTheory.DiscClosure

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}


variable (E N) in
def autSub : Submodule ℂ (Sm E N) where
  carrier := {φ | IsAutForm φ}
  zero_mem' := isAutForm_const (Submodule.zero_mem _)
  add_mem' := fun {φ ψ} h h' => by
    simpa using GlobalTheory.CuspFormLin.isAutForm_smul_add 1 h h'
  smul_mem' := fun c φ h => by
    simpa using GlobalTheory.CuspFormLin.isAutForm_smul_add c h (isAutForm_const (Submodule.zero_mem _))


variable (μ : Measure (GA E N)) in
def squareIntegrableSmoothSubmoduleGL : Submodule ℂ (Sm E N) where
  carrier := {φ | MemL2Quotient (latticeGL E N) μ φ.1}
  zero_mem' := ⟨fun _ _ _ => rfl, MemLp.zero⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ hγ g => by
    change φ.1 (γ * g) + ψ.1 (γ * g) = φ.1 g + ψ.1 g
    rw [h.1 γ hγ g, h'.1 γ hγ g], h.2.add h'.2⟩
  smul_mem' := fun c φ h => ⟨fun γ hγ g => by
    change c * φ.1 (γ * g) = c * φ.1 g
    rw [h.1 γ hγ g], h.2.const_smul c⟩

def stabSub (φ : Sm E N) : Subgroup (GL (Fin N) (Af E)) where
  carrier := {k | finRep E N k φ = φ}
  mul_mem' := fun {a b} ha hb => by
    change finRep E N (a * b) φ = φ
    have ha' : finRep E N a φ = φ := ha
    have hb' : finRep E N b φ = φ := hb
    rw [map_mul, Module.End.mul_apply, hb', ha']
  one_mem' := by
    change finRep E N 1 φ = φ
    rw [map_one]; rfl
  inv_mem' := fun {a} ha => by
    change finRep E N a⁻¹ φ = φ
    have ha' : finRep E N a φ = φ := ha
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

end GlobalTheory.DiscClosure

namespace GlobalTheory.DiscClosure

open GlobalTheory.PRep GlobalTheory.CuspRep.LocEx GlobalTheory.DiscLocEx

end GlobalTheory.DiscClosure
