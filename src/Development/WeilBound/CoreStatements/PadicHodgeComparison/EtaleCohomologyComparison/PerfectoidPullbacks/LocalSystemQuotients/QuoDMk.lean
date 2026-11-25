module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
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

namespace CrystallineSemistableComparison.Ls

variable {W : Type} [CommRing W]

abbrev lpow (l : ℕ) (M : Type 1) [AddCommGroup M] [Module W M] (n : ℕ) : Submodule W M :=
  LinearMap.range (((l : W) ^ n) • LinearMap.id : M →ₗ[W] M)

def quo (l : ℕ) (K : Cx.{1} W) (n : ℕ) : Cx.{1} W where
  X i := K.X i ⧸ lpow l (K.X i) n
  d i := Submodule.mapQ _ _ (K.d i) (by
    rintro _ ⟨y, rfl⟩
    exact ⟨K.d i y, by simp⟩)
  dd i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [Submodule.mapQ_apply, K.dd]

def red (l : ℕ) (K : Cx.{1} W) (n : ℕ) : Cx.Hom (quo l K (n + 1)) (quo l K n) (RingHom.id W) where
  f i := Submodule.mapQ _ _ LinearMap.id (by
    rintro _ ⟨y, rfl⟩
    exact ⟨(l : W) • y, by simp [pow_succ, mul_smul, smul_comm ((l : W) ^ n) (l : W) y]⟩)
  comm i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

def qsys (l : ℕ) (K : Cx.{1} W) (j : ℕ) : Sys.{1} W where
  M n := (quo l K n).H j
  r n := (red l K n).mapH j

def redg (l : ℕ) (K : Cx.{1} W) {b c : ℕ} (h : b ≤ c) : Cx.Hom (quo l K c) (quo l K b) (RingHom.id W) where
  f i := Submodule.mapQ _ _ LinearMap.id (by
    rintro _ ⟨y, rfl⟩
    exact ⟨((l : W) ^ (c - b)) • y, by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← pow_add, Nat.add_sub_cancel' h]⟩)
  comm i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

def nug (l : ℕ) (K : Cx.{1} W) {a c : ℕ} (h : a ≤ c) : Cx.Hom (quo l K a) (quo l K c) (RingHom.id W) where
  f i := Submodule.mapQ _ _ (((l : W) ^ (c - a)) • LinearMap.id) (by
    rintro _ ⟨y, rfl⟩
    exact ⟨y, by simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← pow_add, Nat.sub_add_cancel h]⟩)
  comm i x := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk ((K.d i).map_smul _ x)

end CrystallineSemistableComparison.Ls

end
