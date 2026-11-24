module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.LKCount

def LeftCosets {Γ G : Type} [Group Γ] [Group G] (_ι : Γ →* G) (K : Subgroup G) : Type := G ⧸ K

namespace LeftCosets

variable {Γ G : Type} [Group Γ] [Group G] (ι : Γ →* G) (K : Subgroup G)

instance : MulAction Γ (LeftCosets ι K) := MulAction.compHom (G ⧸ K) ι

def mk (x : G) : LeftCosets ι K := ((x : G ⧸ K) : G ⧸ K)

def rep (y : LeftCosets ι K) : G := Quotient.out (y : G ⧸ K)

variable {ι K}

theorem mk_rep (y : LeftCosets ι K) : mk ι K (rep ι K y) = y :=
  QuotientGroup.out_eq' (s := K) (y : G ⧸ K)

theorem mk_eq_mk {x y : G} : mk ι K x = mk ι K y ↔ x⁻¹ * y ∈ K :=
  QuotientGroup.eq

theorem smul_mk (η : Γ) (x : G) : η • mk ι K x = mk ι K (ι η * x) := rfl

theorem rep_mk (x : G) : ∃ k ∈ K, rep ι K (mk ι K x) = x * k := by
  have h : mk ι K x = mk ι K (rep ι K (mk ι K x)) := (mk_rep _).symm
  rw [mk_eq_mk] at h
  exact ⟨_, h, by group⟩

theorem mem_map_conj {x g : G} : g ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * g * x ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem stabilizer_mk (x : G) :
    MulAction.stabilizer Γ (mk ι K x) = (K.map (MulAut.conj x).toMonoidHom).comap ι := by
  ext η
  rw [MulAction.mem_stabilizer_iff, smul_mk, mk_eq_mk, Subgroup.mem_comap, mem_map_conj]
  constructor
  · intro h
    have := K.inv_mem h
    simpa [mul_assoc] using this
  · intro h
    have := K.inv_mem h
    simpa [mul_assoc] using this

end LeftCosets

section Terms

variable {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂]

theorem stab_eq_stabilizer (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (x : G₁ × G₂) :
    stab ι₁ ι₂ K₁ K₂ x = MulAction.stabilizer Γ (LeftCosets.mk (ι₁.prod ι₂) (K₁.prod K₂) x) := by
  rw [LeftCosets.stabilizer_mk]
  ext η
  simp only [stab, Subgroup.mem_inf, Subgroup.mem_comap, LeftCosets.mem_map_conj, Subgroup.mem_prod,
    MonoidHom.prod_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]

end Terms

end GlobalTheory.LKCount
