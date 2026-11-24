module

import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.ScalarMultipleMembership

theorem exists_smul_mem {Ks WL : Type} [Field Ks] [NumberField Ks] [AddCommGroup WL] [Module Ks WL]
    [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL]
    (M : Submodule (NumberField.RingOfIntegers Ks) WL) (x : WL)
    (hx : x ∈ Submodule.span Ks (M : Set WL)) :
    ∃ a : NumberField.RingOfIntegers Ks, a ≠ 0 ∧ a • x ∈ M := by
  apply Formalism.L2.SG.Pf.LatEx.exists_smul_mem_of_mem_span <;> assumption

theorem main {LL Ks WL G : Type} [inst : Field LL] [NumberField LL] [inst_2 : Field Ks] [inst_3 : NumberField Ks] [inst_4 : Algebra Ks LL] [inst_5 : AddCommGroup WL] [inst_6 : Module LL WL] [inst_7 : Module Ks WL] [IsScalarTower Ks LL WL] [inst_9 : Module (NumberField.RingOfIntegers Ks) WL] [inst_10 : IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {W : (LL →+* ℂ) → Type} [inst_11 : (σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [inst_12 : (σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [inst_13 : Group G] (Φ : Formalism.IndefR.Arith.FormsL LL Ks WL W G)
    (h : Submodule.span Ks (↑(Formalism.IndefR.Arith.FormsL.MK Φ) : Set WL) = Formalism.IndefR.Arith.FormsL.WK Φ) :
    ∀ x ∈ Formalism.IndefR.Arith.FormsL.WK Φ, ∃ (a : NumberField.RingOfIntegers Ks), a ≠ (0 : NumberField.RingOfIntegers Ks) ∧ a • x ∈ Formalism.IndefR.Arith.FormsL.MK Φ := by
  intro x hx
  rw [← h] at hx
  exact exists_smul_mem _ x hx

end GlobalTheory.ScalarMultipleMembership
