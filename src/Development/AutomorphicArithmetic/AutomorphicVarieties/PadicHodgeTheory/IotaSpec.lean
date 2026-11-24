module

public import Formalism.ConjugateSelfDual.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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

namespace UpperTheory.V.Loc

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {Ω : Type} [Field Ω] [CharZero Ω] {v : ℕ} [Fact v.Prime]

def placeJ (j : Ω →+* Om v) : ValuationSubring Ω := (Valued.v : Valuation (Om v) NNReal).valuationSubring.comap j

variable [IsAlgClosure ℚ Ω]

def iota (j : Ω →+* Om v) : GQ v →* G ℚ Ω :=
  letI : Algebra Ω (Om v) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (Om v) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Om v) Ω).comp
    { toFun := fun σ => σ.restrictScalars ℚ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem iota_spec (j : Ω →+* Om v) (σ : GQ v) (y : Ω) : j (iota j σ y) = σ (j y) := by
  letI : Algebra Ω (Om v) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (Om v) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) Ω y

theorem exists_emb : Nonempty (Ω →+* Om v) := ⟨(IsAlgClosed.lift (R := ℚ) (S := Ω) (M := Om v)).toRingHom⟩

end UpperTheory.V.Loc
