module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieDefs
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfConjPoints

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def pairSubst {τ : Type} (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def hAt (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : MvPowerSeries τ C :=
  MvPowerSeries.subst (pairSubst a b) X.h

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rs (j : Fin 2) (c : C) : MvPowerSeries (Fin 2) C →+* MvPowerSeries (Fin 2) C :=
  MvPowerSeries.rescale (fun i => if i = j then c else 1)

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

theorem hsX (j : Fin 2) : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

theorem inV_cc (j : Fin 2) {f : PowerSeries C} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (inV j f) = 0 :=
  constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) hf

theorem rescale_inV (w : Fin 2 → C) (j : Fin 2) (f : PowerSeries C) :
    MvPowerSeries.rescale w (inV j f) = inV j (PowerSeries.rescale (w j) f) := by
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  have hc : MvPowerSeries.HasSubst (fun _ : Unit => (w j • PowerSeries.X : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by
      show MvPowerSeries.constantCoeff (w j • (PowerSeries.X : PowerSeries C)) = 0
      rw [MvPowerSeries.smul_eq_C_mul, map_mul,
        show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries C) = 0 from MvPowerSeries.constantCoeff_X (), mul_zero]
  unfold inV
  rw [MvPowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst]
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (hsX j) hw, MvPowerSeries.subst_comp_subst_apply hc (hsX j)]
  congr 1
  funext u
  rw [MvPowerSeries.subst_X hw, ← MvPowerSeries.coe_substAlgHom (hsX j), map_smul, MvPowerSeries.coe_substAlgHom (hsX j)]
  have h1 : MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 2) C)) (PowerSeries.X : PowerSeries C) =
      MvPowerSeries.X j := MvPowerSeries.subst_X (hsX j) ()
  rw [h1]
  rfl

theorem rescale_HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (w : Fin 2 → C) :
    MvPowerSeries.rescale w (HH X x z) = HH X (rc (w 0) x) (rc (w 1) z) := by
  have hP : MvPowerSeries.HasSubst (pairSubst (fun i => inV 0 (x i)) (fun i => inV 1 (z i))) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ?_
    unfold pairSubst
    split_ifs
    · exact inV_cc 0 (hx q.2)
    · exact inV_cc 1 (hz q.2)
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold HH hAt
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hP hw]
  congr 1
  funext q
  rw [← MvPowerSeries.rescale_eq_subst]
  unfold pairSubst rc
  split_ifs
  · exact rescale_inV w 0 (x q.2)
  · exact rescale_inV w 1 (z q.2)

end SelfConjPoints


open SelfConjPoints in
theorem r1sHResc (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (c : C) :
    HH X (rc c x) z = rs 0 c (HH X x z) ∧ HH X x (rc c z) = rs 1 c (HH X x z) := by
  have e1 : ∀ y : κ → PowerSeries C, rc 1 y = y := fun y => by
    funext i; unfold rc; rw [PowerSeries.rescale_one]; rfl
  refine ⟨?_, ?_⟩
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]
  · unfold rs
    rw [rescale_HH X x z hx hz]
    simp [e1]

end Formalism.L2.FormalSeriesBounds
