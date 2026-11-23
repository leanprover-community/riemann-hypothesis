module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Kloc
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

def locVal (ι : Ω →+* PadicAlgCl p) : Valuation (Kloc F ι) NNReal :=
  (PadicAlgCl.valued p).v.comap (algebraMap (Kloc F ι) (PadicAlgCl p))

theorem locVal_apply (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) : ((locVal ι x : NNReal) : ℝ) = ‖(x : PadicAlgCl p)‖ :=
  rfl

@[instance_reducible]
def locRel (ι : Ω →+* PadicAlgCl p) : ValuativeRel (Kloc F ι) := .ofValuation (locVal ι)

attribute [local instance] locRel

theorem locVal_compat (ι : Ω →+* PadicAlgCl p) : (locVal (F := F) ι).Compatible := Valuation.Compatible.ofValuation _

theorem valuation_lt_iff_Kloc (ι : Ω →+* PadicAlgCl p) (x y : Kloc F ι) :
    valuation (Kloc F ι) x < valuation (Kloc F ι) y ↔ ‖(x : PadicAlgCl p)‖ < ‖(y : PadicAlgCl p)‖ := by
  have := locVal_compat (F := F) ι
  rw [(ValuativeRel.isEquiv (valuation (Kloc F ι)) (locVal ι)).lt_iff_lt, ← NNReal.coe_lt_coe,
    locVal_apply, locVal_apply]

theorem valuation_le_iff_Kloc (ι : Ω →+* PadicAlgCl p) (x y : Kloc F ι) :
    valuation (Kloc F ι) x ≤ valuation (Kloc F ι) y ↔ ‖(x : PadicAlgCl p)‖ ≤ ‖(y : PadicAlgCl p)‖ := by
  rw [← not_lt, valuation_lt_iff_Kloc, not_lt]

theorem mem_integer_Kloc (ι : Ω →+* PadicAlgCl p) (x : Kloc F ι) :
    x ∈ 𝒪[Kloc F ι] ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by
  have h := valuation_le_iff_Kloc ι x 1
  rw [map_one] at h
  rw [Valuation.mem_integer_iff, h]
  simp

end ReciprocityTheory.Neutral.Cmp
