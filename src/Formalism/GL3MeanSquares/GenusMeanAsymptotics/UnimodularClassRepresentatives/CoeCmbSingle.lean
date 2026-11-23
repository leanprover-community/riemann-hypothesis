module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def cmb (b : Basis κ K V) (c : κ → 𝓞 K) : spanO b := (bO b).equivFun.symm c

theorem coe_cmb (b : Basis κ K V) (c : κ → 𝓞 K) : (cmb b c : V) = ∑ l, c l • b l := by
  rw [cmb, Basis.equivFun_symm_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [Submodule.coe_smul, bO_apply]

theorem crd_cmb (b : Basis κ K V) (c : κ → 𝓞 K) : crd b (cmb b c) = c :=
  (bO b).equivFun.apply_symm_apply c

theorem cmb_crd (b : Basis κ K V) (y : spanO b) : cmb b (crd b y) = y :=
  (bO b).equivFun.symm_apply_apply y

def inA (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (b : Basis κ K V) : spanO b →ₗ[𝓞 K] ↥(locF 𝔭 (spanO b)) :=
  Submodule.inclusion (le_locF 𝔭 (spanO b))

theorem coe_inA (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (b : Basis κ K V) (y : spanO b) : (inA 𝔭 b y : V) = y := rfl

abbrev QA (𝔭 : Ideal (𝓞 F)) (b : Basis κ K V) (k : ℕ) : Type :=
  ↥(locF 𝔭 (spanO b)) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 (spanO b)))

theorem mk_eq_iff {𝔭 : Ideal (𝓞 F)} (b : Basis κ K V) (k : ℕ) (x y : ↥(locF 𝔭 (spanO b))) :
    (Submodule.Quotient.mk x : QA 𝔭 b k) = Submodule.Quotient.mk y ↔
      (x : V) - y ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  rw [Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  rfl

theorem quotLocF_mk' {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (y : spanO b) : quotLocF h𝔭 (spanO b) k (Submodule.Quotient.mk y) = Submodule.Quotient.mk (inA 𝔭 b y) :=
  rfl

theorem exists_cmb {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (q : QA 𝔭 b k) : ∃ c : κ → 𝓞 K, q = Submodule.Quotient.mk (inA 𝔭 b (cmb b c)) := by
  obtain ⟨q₀, rfl⟩ := (quotLocF h𝔭 (spanO b) k).surjective q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q₀
  exact ⟨crd b y, by rw [cmb_crd, quotLocF_mk']⟩

theorem cmb_eq_sum (b : Basis κ K V) (c : κ → 𝓞 K) : cmb b c = ∑ i, c i • cmb b (Pi.single i 1) := by
  apply (bO b).equivFun.injective
  show crd b _ = crd b _
  rw [crd_cmb]
  have : crd b (∑ i, c i • cmb b (Pi.single i 1)) = ∑ i, c i • crd b (cmb b (Pi.single i 1)) := by
    unfold crd

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [this]
  funext l
  simp [crd_cmb, Pi.single_apply]

theorem end_apply_cmb {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) (Y : Matrix κ κ (𝓞 K))
    (hXY : ∀ i, X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))) =
      Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i))) (c : κ → 𝓞 K) :
    X (Submodule.Quotient.mk (inA 𝔭 b (cmb b c))) = Submodule.Quotient.mk (inA 𝔭 b (cmb b (Y *ᵥ c))) := by
  have h1 : cmb b (Y *ᵥ c) = ∑ i, c i • cmb b fun l => Y l i := by
    apply (bO b).equivFun.injective
    show crd b _ = crd b _
    have : crd b (∑ i, c i • cmb b fun l => Y l i) = ∑ i, c i • crd b (cmb b fun l => Y l i) := by
      unfold crd

      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    rw [this, crd_cmb]
    funext l
    simp [crd_cmb, mulVec, dotProduct, mul_comm]
  rw [h1, cmb_eq_sum b c]
  simp only [← Submodule.mkQ_apply] at hXY ⊢

  simp only [map_sum, map_smul, hXY]

end Formalism.HermitianLattices.Ext.L3.HU
