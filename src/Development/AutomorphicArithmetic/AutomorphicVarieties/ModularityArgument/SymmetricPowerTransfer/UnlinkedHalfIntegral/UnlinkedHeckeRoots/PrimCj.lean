module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

namespace UpperTheory.V.Z.Sym.Unl

private theorem ker_cj {N : ℕ} (σ : ℂ ≃+* ℂ) (χ : DirichletCharacter ℂ N) :
    (cj σ χ).toUnitHom.ker = χ.toUnitHom.ker := by
  ext x
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, cj, MulChar.ringHomComp_apply]
  exact map_eq_one_iff σ σ.injective

theorem primCj : PrimCj := by
  intro N _ χ σ hχ
  have key : ∀ d : ℕ, (cj σ χ).FactorsThrough d ↔ χ.FactorsThrough d := by
    intro d
    constructor
    · intro h
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd, ← ker_cj σ χ]
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
    · intro h
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd, ker_cj σ χ]
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
  have hc : (cj σ χ).conductor = χ.conductor := by
    unfold DirichletCharacter.conductor DirichletCharacter.conductorSet
    congr 1
    ext d
    exact key d
  unfold DirichletCharacter.IsPrimitive at hχ ⊢
  rw [hc]
  exact hχ

end UpperTheory.V.Z.Sym.Unl
