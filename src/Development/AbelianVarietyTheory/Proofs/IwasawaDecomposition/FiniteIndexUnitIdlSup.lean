module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.ClassNumber
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.UnitIndex

variable (L : Type) [Field L] [NumberField L]

def finIdele : Ideles L →* (FiniteAdeleRing (𝓞 L) L)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def idealHom : (FiniteAdeleRing (𝓞 L) L)ˣ →* FractionalIdeal (𝓞 L)⁰ L where
  toFun := GlobalTheory.Idele.idealOf
  map_one' := GlobalTheory.Idele.idealOf_one
  map_mul' := GlobalTheory.Idele.idealOf_mul

def classHom : Ideles L →* ClassGroup (𝓞 L) :=
  (ClassGroup.mk L).comp ((idealHom L).comp (finIdele L)).toHomUnits

theorem ker_classHom_le : (classHom L).ker ≤ unitIdl L ⊔ (diagUnits L).range := by
  intro a ha
  have h1 : ClassGroup.mk L (((idealHom L).comp (finIdele L)).toHomUnits a) = 1 := ha
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  have hx' : GlobalTheory.Idele.idealOf (finIdele L a) = FractionalIdeal.spanSingleton (𝓞 L)⁰ x := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx'.trans (FractionalIdeal.spanSingleton_zero))
  have hd : finIdele L (diagUnits L (Units.mk0 x hx0)) =
      FiniteAdeleRing.unitEmbedding (𝓞 L) L (Units.mk0 x hx0) := Units.ext rfl
  have hu : a * (diagUnits L (Units.mk0 x hx0))⁻¹ ∈ unitIdl L := by
    refine (GlobalTheory.Idele.smul_eq_self_iff (finIdele L (a * (diagUnits L (Units.mk0 x hx0))⁻¹))
      (I := 1) one_ne_zero).1 ?_
    rw [GlobalTheory.Idele.smul_one_eq, map_mul, map_inv, GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, hd,
      GlobalTheory.Idele.idealOf_unitEmbedding, hx']
    exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)
  have : a = a * (diagUnits L (Units.mk0 x hx0))⁻¹ * diagUnits L (Units.mk0 x hx0) := by simp
  rw [this]
  exact Subgroup.mul_mem_sup hu ⟨_, rfl⟩


open Classical in
theorem finiteIndex_unitIdl_sup : ∀ (L : Type) [Field L] [NumberField L],
    (unitIdl L ⊔ (diagUnits L).range).FiniteIndex := by
  intro L _ _
  have : (classHom L).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  exact Subgroup.finiteIndex_of_le (ker_classHom_le L)

end GlobalTheory.Mem.UnitIndex
