module

public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolReal
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolBridge
public import GroundTheory.ProfiniteCohomology.CartierDual
public import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory GroundTheory.GroupCoh

attribute [local instance 2000] Rep.hV2

section TateZero

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Fintype G]

def normClasses (A : Rep k G) [IsDiscreteRep A] : Submodule k (cohomology A 0) :=
  (normRangeInvariants A).map (H0Iso A).inv.hom

theorem mem_normClasses_iff (A : Rep k G) [IsDiscreteRep A] (x : cohomology A 0) :
    x ∈ normClasses A ↔ ∃ a : A, ∃ h : A.ρ.norm a ∈ A.ρ.invariants,
      x = (H0Iso A).inv.hom ⟨A.ρ.norm a, h⟩ := by
  constructor
  · rintro ⟨y, ⟨a, ha⟩, rfl⟩
    refine ⟨a, ha ▸ y.2, ?_⟩
    congr 1
    exact Subtype.ext ha.symm
  · rintro ⟨a, h, rfl⟩
    exact ⟨⟨A.ρ.norm a, h⟩, ⟨a, rfl⟩, rfl⟩

abbrev cohomologyTateZero (A : Rep k G) [IsDiscreteRep A] : Type :=
  cohomology A 0 ⧸ normClasses A

end TateZero

section Pairing

variable (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))

def realInv : cohomology (galUnits.{0} F Ω) 2 →+ QZ :=
  (quadraticInv F Ω h2 hN).comp (cohomologyULiftIntAddEquiv (galUnits.{0} F Ω) 2).toAddMonoidHom

theorem realInv_apply (x : cohomology (galUnits.{0} F Ω) 2) :
    realInv F Ω h2 hN x = quadraticInv F Ω h2 hN (cohomologyULiftIntAddEquiv (galUnits.{0} F Ω) 2 x) :=
  rfl

def realDualityPairing (M : Rep (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M] {r s : ℕ}
    (h : r + s = 2) : cohomology M r →+ cohomology (cartierDual F Ω M) s →+ QZ :=
  (AddMonoidHom.compHom (realInv F Ω h2 hN)).comp
    (bilinAddHom (cupPairing (cartierPairing F Ω M) h))

theorem realDualityPairing_apply (M : Rep (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]
    {r s : ℕ} (h : r + s = 2) (x : cohomology M r) (y : cohomology (cartierDual F Ω M) s) :
    realDualityPairing F Ω h2 hN M h x y =
      realInv F Ω h2 hN (cupPairing (cartierPairing F Ω M) h x y) :=
  rfl

end Pairing

end GroundTheory.ProfCoh
