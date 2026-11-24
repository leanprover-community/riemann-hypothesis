module

public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BigCellLocal
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

section Loc

variable (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (c : L →+* L) (m : ℕ)

def GW : Subgroup (GL (Fin m ⊕ Fin m) L) where
  carrier := {g | Iso c (Wm L (Fin m)) (Wm L (Fin m)) (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)}
  one_mem' := by
    show Iso c _ _ ((1 : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    simp [Iso, Matrix.map_one _ (map_zero c) (map_one c)]
  mul_mem' := fun {a b} ha hb => by
    show Iso c _ _ ((a * b : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    rw [Units.val_mul]; exact Iso.mul ha hb
  inv_mem' := fun {a} ha => by
    show Iso c _ _ ((a⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L)
    exact Iso.inv ha (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])

def IntGL : Subgroup (GL (Fin m ⊕ Fin m) L) := (Matrix.GeneralLinearGroup.map (intL L).subtype).range

def KW : Subgroup (GL (Fin m ⊕ Fin m) L) := GW L c m ⊓ IntGL L m

def PW : Subgroup (GL (Fin m ⊕ Fin m) L) :=
  GW L c m ⊓ GlobalTheory.LGrp.blockQ L (GlobalTheory.LGrp.twoBlocks (Fin m) (Fin m))

abbrev KPW : Subgroup (GL (Fin m ⊕ Fin m) L) := PW L c m ⊓ KW L c m

def levM (t : GL (Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L :=
  fromBlocks (t : Matrix (Fin m) (Fin m) L) 0 0 (((t⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L)ᵀ.map c)

def lev : GL (Fin m) L →* GL (Fin m ⊕ Fin m) L where
  toFun t := ⟨levM L c m t, levM L c m t⁻¹,
    by
      have h1 : (t : Matrix (Fin m) (Fin m) L) * ((t⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) = 1 := Units.mul_inv t
      simp only [levM, fromBlocks_multiply, inv_inv, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      rw [h1, ← Matrix.map_mul, ← Matrix.transpose_mul, h1, Matrix.transpose_one,
        Matrix.map_one _ (map_zero c) (map_one c), fromBlocks_one],
    by
      have h2 : ((t⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) * (t : Matrix (Fin m) (Fin m) L) = 1 := Units.inv_mul t
      simp only [levM, fromBlocks_multiply, inv_inv, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
      rw [h2, ← Matrix.map_mul, ← Matrix.transpose_mul, h2, Matrix.transpose_one,
        Matrix.map_one _ (map_zero c) (map_one c), fromBlocks_one]⟩
  map_one' := by
    ext1
    simp [levM, Matrix.map_one _ (map_zero c) (map_one c), fromBlocks_one]
  map_mul' s t := by
    ext1
    simp only [Units.val_mul, levM, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul]

def zW (x : Lˣ) : GL (Fin m ⊕ Fin m) L :=
  ⟨fromBlocks ((x : L) • 1) 0 0 (((x⁻¹ : Lˣ) : L) • 1), fromBlocks (((x⁻¹ : Lˣ) : L) • 1) 0 0 ((x : L) • 1),
    by simp [fromBlocks_multiply, smul_smul, fromBlocks_one],
    by simp [fromBlocks_multiply, smul_smul, fromBlocks_one]⟩

def LocModSt : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q →
    ∀ (m : ℕ), ∀ p ∈ PW L c m,
      ((((KPW L c m).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (KPW L c m) : ℕ) : ℝ) =
        (q : ℝ) ^ (-(2 * (m : ℤ) * ordL (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L).toBlocks₁₁.det)) *
        ((((KPW L c m).map (MulAut.conj p).toMonoidHom).relIndex (KPW L c m) : ℕ) : ℝ)

end Loc

end PositivityTheory.Sph.M2

end
