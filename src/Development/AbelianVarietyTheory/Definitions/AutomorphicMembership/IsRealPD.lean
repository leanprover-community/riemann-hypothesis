module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
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
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per
variable {l : ℕ} [Fact l.Prime]

def ringsOf (C : Core l) : LocRings l :=
  letI aU : Algebra ↥(MaximalUnramifiedExtension l) (Per.Bcris l) := C.u.toAlgebra
  letI aQ : Algebra ℚ_[l] (Per.Bcris l) := (C.u.comp (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))).toAlgebra
  letI aO : Algebra (Om l) (Per.BdR l) := ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o).toAlgebra
  letI aQ' : Algebra ℚ_[l] (Per.BdR l) :=
    (((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o).comp (algebraMap ℚ_[l] (Om l))).toAlgebra
  { B := Per.Bcris l
    BdR := Per.BdR l
    aQB := aQ
    aUB := aU
    tUB := IsScalarTower.of_algebraMap_eq fun _ => rfl
    aOdR := aO
    aQdR := aQ'
    tQdR := IsScalarTower.of_algebraMap_eq fun _ => rfl }

def eB (C : Core l) : (ringsOf C).B ≃+* Per.Bcris l := RingEquiv.refl (Per.Bcris l)

def eD (C : Core l) : (ringsOf C).BdR ≃+* Per.BdR l := RingEquiv.refl (Per.BdR l)

structure IsRealPD (C : Core l) (K : FinExt l)
    (PD : WeaklyAdmissibleFiltrations.PeriodData ↥(GK K) ℚ_[l] ↥(K0 K) ↥K.1 (ringsOf C).B (ringsOf C).BdR) : Prop where
  p : PD.p = l
  actB : ∀ g b, eB C (PD.actB g b) = Per.σB (g : GQ l) (eB C b)
  actdR : ∀ g b, eD C (PD.actdR g b) = Per.σD (g : GQ l) (eD C b)
  φ : ∀ b, eB C (PD.φ b) = Per.φB l (eB C b)
  ι : ∀ b, eD C (PD.ι b) = C.ι (eB C b)
  t : eB C PD.t = algebraMap (Per.Acris l) (Per.Bcris l) C.t
  χ : ∀ g, ((PD.χ g : ℚ_[l]ˣ) : ℚ_[l]) = ((C.χ (g : GQ l) : ℤ_[l]) : ℚ_[l])
  fil : ∀ a x, x ∈ PD.Fil a ↔ eD C x ∈ Per.FilD l a
  σ : ∀ (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) = (x : Om l) →
    ((PD.σ x : ↥(K0 K)) : Om l) = ((C.σ c : ↥(MaximalUnramifiedExtension l)) : Om l)

end GlobalTheory.MemLoc
