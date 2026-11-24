module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDualC
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.LFun

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem invT_val_eq (g : GA E a) : (invT a (Ad E) g).val = (g.valᵀ)⁻¹ := by
  change (g⁻¹).valᵀ = _
  rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv]

theorem invT_scalar {R : Type} [CommRing R] (z : Rˣ) :
    invT a R (GeneralLinearGroup.scalar (Fin a) z) = GeneralLinearGroup.scalar (Fin a) z⁻¹ := by
  apply Units.ext
  change ((GeneralLinearGroup.scalar (Fin a) z)⁻¹).valᵀ = _
  rw [← map_inv]
  ext i j
  by_cases h : i = j
  · subst h; simp [GeneralLinearGroup.scalar]
  · simp [GeneralLinearGroup.scalar, h, Ne.symm h]

namespace CuspSub

variable (π : CuspSub E a)

def contra : CuspSub E a := UpperTheory.V.TC.dual π

variable {π} {π' : CuspSub E a}

theorem HasCentral.contra {ω : HChar E} (h : π.HasCentral ω) : π.contra.HasCentral ω⁻¹ := by
  rintro z _ ⟨ψ, hψ, rfl⟩
  change rt E a _ (UpperTheory.V.TC.dualFn E a ψ) = _ • UpperTheory.V.TC.dualFn E a ψ
  rw [UpperTheory.V.TC.rt_dualFn, invT_scalar, h z⁻¹ ψ hψ, map_smul]
  congr 1
  simp

theorem IsUnitary.contra (h : π.IsUnitary) : π.contra.IsUnitary := by
  obtain ⟨ω, h1, h2⟩ := h
  exact ⟨ω⁻¹, h1.inv, h2.contra⟩

end CuspSub

namespace CG

end CG

end GlobalTheory.CuspRep
