module

public import Formalism.LocalToGlobal.Divisibility.QLocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIntegralGLMulRightComplexProductSigma
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
public import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaHalfMulUnrTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValue
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.TypeStar
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Mathlib.NumberTheory.RamificationInertia.Basic
import Formalism.DoubleCosetMeasures.Statement

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockUpperTriangularGLMulDetInv, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfFixedLine, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRepEqBlocks, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIsCompactParahoricGLCompletion, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTame, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricTypeRCMulInvMem, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOne, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlace, Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockUpperTriangularGLMulDetInv =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockUpperTriangularGLMulDetInv", "h": "module\n\npublic import Formalism.LocalToGlobal.Divisibility.QLocTied\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.HQStepBlocks

variable {F : Type} [Field F] {r c : ℕ}

theorem submatrix_eq_fromBlocks (x : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    x.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks (bAA x) (bAD x) (bDA x) (bDD x) := by
  ext (i|i) (j|j) <;> simp [bAA, bAD, bDA, bDD]

theorem submatrix_mul' (x y : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    (x * y).submatrix finSumFinEquiv finSumFinEquiv =
      x.submatrix finSumFinEquiv finSumFinEquiv * y.submatrix finSumFinEquiv finSumFinEquiv := by
  rw [Matrix.submatrix_mul_equiv]

theorem blocks_mul (x y : Matrix (Fin (r + c)) (Fin (r + c)) F) :
    bAA (x * y) = bAA x * bAA y + bAD x * bDA y ∧ bAD (x * y) = bAA x * bAD y + bAD x * bDD y ∧
    bDA (x * y) = bDA x * bAA y + bDD x * bDA y ∧ bDD (x * y) = bDA x * bAD y + bDD x * bDD y := by
  have h := submatrix_mul' x y
  rw [submatrix_eq_fromBlocks, submatrix_eq_fromBlocks, submatrix_eq_fromBlocks,
    fromBlocks_multiply, fromBlocks_inj] at h
  exact h

theorem det_eq_of_bDA_eq_zero (x : Matrix (Fin (r + c)) (Fin (r + c)) F) (hx : bDA x = 0) :
    x.det = (bAA x).det * (bDD x).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv x, submatrix_eq_fromBlocks, hx,
    Matrix.det_fromBlocks_zero₂₁]

theorem main : ∀ (F : Type) [Field F] (r c : ℕ) (p q : GL (Fin (r + c)) F), bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 → bDA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 ∧ bAA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ bDD ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bDD (q : Matrix (Fin (r + c)) (Fin (r + c)) F) ∧ (p : Matrix (Fin (r + c)) (Fin (r + c)) F).det = (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ∧ bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
  intro F _ r c p q hp hq
  obtain ⟨h11, -, h21, h22⟩ := blocks_mul (p : Matrix (Fin (r + c)) (Fin (r + c)) F) (q : Matrix _ _ F)
  refine ⟨?_, ?_, ?_, det_eq_of_bDA_eq_zero _ hp, ?_⟩
  · rw [Units.val_mul, h21, hp, hq]; simp
  · rw [Units.val_mul, h11, hq]; simp
  · rw [Units.val_mul, h22, hp]; simp
  · obtain ⟨k11, -, k21, -⟩ := blocks_mul ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)
      (p : Matrix _ _ F)
    have hone : ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) * (p : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hone, hp, Matrix.mul_zero, add_zero] at k11 k21
    have e11 : bAA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
      ext i j; simp [bAA, Matrix.one_apply]
    have e21 : bDA (1 : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
      ext i j; simp [bDA, Matrix.one_apply, Fin.ext_iff]; omega
    rw [e11] at k11
    rw [e21] at k21
    have hA : bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 :=
      mul_eq_one_comm.mp k11.symm
    calc bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)
        = bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) *
            (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)) := by
          rw [hA, Matrix.mul_one]
      _ = 0 := by rw [← Matrix.mul_assoc, ← k21, Matrix.zero_mul]

end GlobalTheory.HQStepBlocks
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockUpperTriangularGLMulDetInv =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfFixedLine =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfFixedLine", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd\npublic import Mathlib.Analysis.CStarAlgebra.Module.Constructions\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup\nimport Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIntegralGLMulRightComplexProductSigma\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Topology
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.SphCyclic

theorem irreducible_of_fixed_line {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : G →* (V ≃ₗᵢ[ℂ] V)) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (hsm : ∀ x, IsOpen {g | ρ g x = x}) (v : V) (hv : ∀ k ∈ K, ρ k v = v)
    (hcyc : Submodule.span ℂ (Set.range fun g => ρ g v) = ⊤)
    (hline : ∀ x, (∀ k ∈ K, ρ k x = x) → ∃ c : ℂ, x = c • v)
    (W : Submodule ℂ V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  have hmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x) := fun g h x => by rw [map_mul]; rfl
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨w₀, hw₀, hw0⟩ := (Submodule.ne_bot_iff W).1 hne
  obtain ⟨g, hg⟩ : ∃ g, inner ℂ (ρ g v) w₀ ≠ 0 := by
    by_contra h
    push Not at h
    have : ∀ x ∈ Submodule.span ℂ (Set.range fun g => ρ g v), inner ℂ x w₀ = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact h g
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
    exact hw0 (inner_self_eq_zero.1 (this w₀ (hcyc ▸ Submodule.mem_top)))
  set w := ρ g⁻¹ w₀ with hw
  have hwW : w ∈ W := hW _ _ hw₀
  have hvw : inner ℂ v w ≠ 0 := by
    rw [← (ρ g).inner_map_map, hw, ← hmul, mul_inv_cancel, map_one]
    exact hg
  have hlc : IsLocallyConstant fun g : G => ρ g w := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun a => ?_
    have h1 : IsOpen {b : G | ρ (a⁻¹ * b) w = w} := (hsm w).preimage (continuous_const_mul a⁻¹)
    filter_upwards [h1.mem_nhds (show a ∈ {b : G | ρ (a⁻¹ * b) w = w} by simp)] with b hb
    rw [← mul_inv_cancel_left a b, hmul, hb]
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfin : (Set.range fun k : K => ρ k w).Finite :=
    (hlc.comp_continuous continuous_subtype_val).range_finite
  set u := ∑ y ∈ hfin.toFinset, y with hu
  have huW : u ∈ W := W.sum_mem fun y hy => by
    obtain ⟨k, rfl⟩ := hfin.mem_toFinset.1 hy
    exact hW _ _ hwW
  have hufix : ∀ k ∈ K, ρ k u = u := by
    intro k hk

    rw [hu, map_sum]
    refine Finset.sum_bij (fun y _ => ρ k y) ?_ ?_ ?_ fun _ _ => rfl
    · intro y hy
      obtain ⟨l, rfl⟩ := hfin.mem_toFinset.1 hy
      exact hfin.mem_toFinset.2 ⟨⟨k, hk⟩ * l, hmul _ _ _⟩
    · intro y _ z _ h
      exact (ρ k).injective h
    · intro y hy
      obtain ⟨l, rfl⟩ := hfin.mem_toFinset.1 hy
      refine ⟨_, hfin.mem_toFinset.2 ⟨⟨k, hk⟩⁻¹ * l, rfl⟩, ?_⟩
      show ρ k (ρ (k⁻¹ * l) w) = _
      rw [← hmul, mul_inv_cancel_left]
  have hvu : inner ℂ v u ≠ 0 := by
    rw [hu, inner_sum, Finset.sum_congr rfl (g := fun _ => inner ℂ v w), Finset.sum_const, nsmul_eq_mul]
    · refine mul_ne_zero (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨_, hfin.mem_toFinset.2 ⟨1, rfl⟩⟩)) hvw
    · intro y hy
      obtain ⟨l, rfl⟩ := hfin.mem_toFinset.1 hy
      conv_lhs => rw [← hv l l.2]
      exact (ρ l).inner_map_map _ _
  obtain ⟨c, hc⟩ := hline u hufix
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hvu (by rw [hc]; simp)
  have hvW : v ∈ W := (W.smul_mem_iff hc0).1 (hc ▸ huW)
  rw [eq_top_iff, ← hcyc, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  exact hW _ _ hvW

section Cyclic

variable {G : Type} [Group G]

def transl (φ : G → ℂ) : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range fun g x => φ (x * g))

theorem transl_mem {φ f : G → ℂ} (hf : f ∈ transl φ) (g : G) : (fun x => f (x * g)) ∈ transl φ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, rfl⟩ := hf
    exact Submodule.subset_span ⟨g * a, by simp only [mul_assoc]⟩
  | zero => exact zero_mem _
  | add f f' _ _ h h' => exact add_mem h h'
  | smul a f _ h => exact Submodule.smul_mem _ a h

def translEquiv (φ : G → ℂ) (g : G) : transl φ ≃ₗ[ℂ] transl φ where
  toFun f := ⟨fun x => f.1 (x * g), transl_mem f.2 g⟩
  invFun f := ⟨fun x => f.1 (x * g⁻¹), transl_mem f.2 g⁻¹⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := Subtype.ext (funext fun x => by simp)
  right_inv f := Subtype.ext (funext fun x => by simp)

theorem transl_law {φ f : G → ℂ} {p : G} {c : ℂ} (h : ∀ x, φ (p * x) = c * φ x) (hf : f ∈ transl φ) (x : G) :
    f (p * x) = c * f x := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, rfl⟩ := hf
    simp only [mul_assoc, h]
  | zero => simp
  | add f f' _ _ h h' => simp only [Pi.add_apply, h, h', mul_add]
  | smul a f _ h => simp only [Pi.smul_apply, h, smul_eq_mul]; ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem transl_smooth {φ f : G → ℂ} {K : Subgroup G} (hK : IsOpen (K : Set G))
    (h : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (hf : f ∈ transl φ) : ∀ᶠ g in 𝓝 (1 : G), ∀ x, f (x * g) = f x := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, rfl⟩ := hf
    have h1 : IsOpen {g : G | a⁻¹ * g * a ∈ K} := hK.preimage (by fun_prop)
    filter_upwards [h1.mem_nhds (show (1 : G) ∈ {g : G | a⁻¹ * g * a ∈ K} by simp)] with g hg x
    rw [← h (x * a) _ hg]
    congr 1
    group
  | zero => simp
  | add f f' _ _ h h' => filter_upwards [h, h'] with g h h' x; simp only [Pi.add_apply, h, h']
  | smul a f _ h => filter_upwards [h] with g h x; simp only [Pi.smul_apply, h]

theorem continuous_of_smooth {f : G → ℂ} (hf : ∀ᶠ g in 𝓝 (1 : G), ∀ x, f (x * g) = f x) : Continuous f := by
  refine ((IsLocallyConstant.iff_eventually_eq _).2 fun a => ?_).continuous
  have h1 : Filter.Tendsto (fun b : G => a⁻¹ * b) (𝓝 a) (𝓝 1) := by
    have := (continuous_const_mul a⁻¹).tendsto a
    rwa [inv_mul_cancel] at this
  filter_upwards [h1.eventually hf] with b hb
  rw [← hb a, mul_inv_cancel_left]

theorem exists_rep [MeasurableSpace G] [BorelSpace G] [T2Space G] (μ : Measure G) [μ.IsHaarMeasure]
    (K P : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hμ : μ K = 1)
    (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) (ψ : P → ℂ) (δ : P → ℂ) (hδ : ∀ p, conj (ψ p) * ψ p = δ p)
    (φ : G → ℂ) (hφP : ∀ (p : P) x, φ (p * x) = ψ p * φ x) (hφK : ∀ x, ∀ k ∈ K, φ (x * k) = φ x)
    (hφ1 : φ 1 = 1)
    (hinv : ∀ F : G → ℂ, Continuous F → (∀ (p : P) x, F (p * x) = δ p * F x) → ∀ g,
      ∫ x in (K : Set G), F (x * g) ∂μ = ∫ x in (K : Set G), F x ∂μ) :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (ρ : G →* (V ≃ₗᵢ[ℂ] V)),
      (∀ x, IsOpen {g | ρ g x = x}) ∧
      (∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      ∃ v : V, ‖v‖ = 1 ∧ (∀ k ∈ K, ρ k v = v) ∧ ∀ g, inner ℂ v (ρ g v) = ∫ k in (K : Set G), φ (k * g) ∂μ := by
  have hc : ∀ f : transl φ, Continuous f.1 := fun f => continuous_of_smooth (transl_smooth hKo hφK f.2)
  have hc2 : ∀ f f' : transl φ, Continuous fun x => conj (f.1 x) * f'.1 x := fun f f' =>
    (Complex.continuous_conj.comp (hc f)).mul (hc f')
  have hi : ∀ f f' : transl φ, IntegrableOn (fun x => conj (f.1 x) * f'.1 x) K μ := fun f f' =>
    (hc2 f f').continuousOn.integrableOn_compact hKc
  have hsq : ∀ f : transl φ, ∫ x in (K : Set G), conj (f.1 x) * f.1 x ∂μ =
      ((∫ x in (K : Set G), ‖f.1 x‖ ^ 2 ∂μ : ℝ) : ℂ) := fun f => by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Complex.conj_mul']
    push_cast; rfl
  have hφk : ∀ k ∈ K, φ k = 1 := fun k hk => by rw [← one_mul k, hφK 1 k hk, hφ1]
  let core : InnerProductSpace.Core ℂ (transl φ) :=
    { inner := fun f f' => ∫ x in (K : Set G), conj (f.1 x) * f'.1 x ∂μ
      conj_inner_symm := fun f f' => by
        rw [← integral_conj]
        simp only [map_mul, Complex.conj_conj, mul_comm]
      re_inner_nonneg := fun f => by
        rw [hsq]
        exact integral_nonneg fun x => sq_nonneg _
      add_left := fun f f' f'' => by
        rw [← integral_add (hi f f'') (hi f' f'')]
        simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), add_mul]
      smul_left := fun f f' r => by
        rw [← integral_const_mul]
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
      definite := fun f hf => by
        rw [hsq, Complex.ofReal_eq_zero] at hf
        have hn : Continuous fun x => ‖f.1 x‖ ^ 2 := (hc f).norm.pow 2
        have h1 := (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
          (hn.continuousOn.integrableOn_compact hKc)).1 hf
        have h2 := Measure.eqOn_open_of_ae_eq h1 hKo hn.continuousOn continuousOn_const
        refine Subtype.ext (funext fun g => ?_)
        obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
        have h3 : f.1 k = 0 := by simpa using h2 hk
        rw [transl_law (hφP ⟨p, hp⟩) f.2, h3, mul_zero]
        rfl }
  letI : NormedAddCommGroup (transl φ) := InnerProductSpace.Core.toNormedAddCommGroup (cd := core)
  letI : InnerProductSpace ℂ (transl φ) := InnerProductSpace.ofCore core.toCore
  have hin : ∀ f f' : transl φ, inner ℂ f f' = ∫ x in (K : Set G), conj (f.1 x) * f'.1 x ∂μ := fun _ _ => rfl
  have hunit : ∀ g (f f' : transl φ), inner ℂ (translEquiv φ g f) (translEquiv φ g f') = inner ℂ f f' := by
    intro g f f'
    refine hinv (fun x => conj (f.1 x) * f'.1 x) (hc2 f f') (fun p x => ?_) g
    simp only [transl_law (hφP p) f.2, transl_law (hφP p) f'.2, map_mul, ← hδ]
    ring
  let ρ : G →* (transl φ ≃ₗᵢ[ℂ] transl φ) := MonoidHom.mk'
    (fun g => (translEquiv φ g).isometryOfInner (hunit g)) fun g h =>
      LinearIsometryEquiv.ext fun f => Subtype.ext (funext fun x => congrArg f.1 (mul_assoc x g h).symm)
  have hρ : ∀ g (f : transl φ) x, (ρ g f).1 x = f.1 (x * g) := fun _ _ _ => rfl
  let v : transl φ := ⟨φ, Submodule.subset_span ⟨1, by simp⟩⟩
  have hsm : ∀ x, IsOpen {g | ρ g x = x} := fun f => by
    let S : Subgroup G :=
      { carrier := {g | ρ g f = f}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          show ρ (a * b) f = f
          rw [map_mul]
          exact (congrArg (ρ a) hb).trans ha
        inv_mem' := fun {a} ha => by
          show ρ a⁻¹ f = f
          rw [map_inv]
          exact (ρ a).symm_apply_eq.2 ha.symm }
    refine S.isOpen_of_mem_nhds (g := 1) ?_
    filter_upwards [transl_smooth hKo hφK f.2] with g hg
    exact Subtype.ext (funext hg)
  have hv : ∀ k ∈ K, ρ k v = v := fun k hk => Subtype.ext (funext fun x => hφK x k hk)
  have hcoef : ∀ g, inner ℂ v (ρ g v) = ∫ k in (K : Set G), φ (k * g) ∂μ := fun g => by
    rw [hin]
    refine setIntegral_congr_fun hKo.measurableSet fun k hk => ?_
    show conj (φ k) * φ (k * g) = _
    rw [hφk k hk, map_one, one_mul]
  refine ⟨transl φ, inferInstance, inferInstance, ρ, hsm, irreducible_of_fixed_line ρ K hKc hsm v hv ?_ ?_,
    v, ?_, hv, hcoef⟩
  · apply Submodule.map_injective_of_injective (transl φ).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    rfl
  · intro f hf
    refine ⟨f.1 1, Subtype.ext (funext fun g => ?_)⟩
    obtain ⟨p, hp, k, hk, rfl⟩ := hPK g
    have h1 : f.1 k = f.1 1 := by rw [← one_mul k, ← hρ, hf k hk]
    show _ = f.1 1 * φ (p * k)
    rw [transl_law (hφP ⟨p, hp⟩) f.2, hφP ⟨p, hp⟩, h1, hφk k hk, mul_one, mul_comm]
  · have h1 := hcoef 1
    rw [map_one, setIntegral_congr_fun hKo.measurableSet (g := fun _ => (1 : ℂ))
      (fun k hk => by simpa using hφk k hk), setIntegral_const, Measure.real, hμ] at h1
    have h2 : inner ℂ v v = 1 := by simpa using h1
    rw [inner_self_eq_norm_sq_to_K] at h2
    have h3 : ‖v‖ ^ 2 = 1 := Complex.ofReal_eq_one.1 (by rw [Complex.ofReal_pow]; exact h2)
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

end Cyclic

end GlobalTheory.SphCyclic

namespace GlobalTheory.SphCyclic

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix ValuativeRel

theorem exists_sphFn {G : Type} [Group G] (K P : Subgroup G) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (ψ : P →* ℂˣ) (hψ : ∀ p : P, (p : G) ∈ K → ψ p = 1) :
    ∃ φ : G → ℂ, (∀ (p : P) x, φ (p * x) = ψ p * φ x) ∧ (∀ x, ∀ k ∈ K, φ (x * k) = φ x) ∧ φ 1 = 1 := by
  choose p hp u hu hpu using hPK
  have key : ∀ (q : P), ∀ k ∈ K, ψ ⟨p (q * k), hp _⟩ = ψ q := by
    intro q k hk
    have h1 : ((q⁻¹ * ⟨p (q * k), hp _⟩ : P) : G) = k * (u (q * k))⁻¹ := by
      show (q : G)⁻¹ * p (q * k) = _
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, ← hpu]
    have h2 := hψ _ (h1 ▸ mul_mem hk (inv_mem (hu _)))
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2.symm
  have key2 : ∀ (q : P) x, ∀ k ∈ K, ψ ⟨p (q * x * k), hp _⟩ = ψ q * ψ ⟨p x, hp _⟩ := by
    intro q x k hk
    have h1 : q * x * k = ((q * ⟨p x, hp x⟩ : P) : G) * (u x * k) := by
      conv_lhs => rw [hpu x]
      simp only [Subgroup.coe_mul, mul_assoc]
    have h2 := key (q * ⟨p x, hp x⟩) _ (mul_mem (hu x) hk)
    simp only [← h1] at h2
    rw [h2, map_mul]
  refine ⟨fun g => ψ ⟨p g, hp g⟩, fun q x => ?_, fun x k hk => ?_, ?_⟩
  · have := key2 q x 1 (one_mem _)
    simp only [mul_one] at this
    simp only [this, Units.val_mul]
  · have := key2 1 x k hk
    simp only [OneMemClass.coe_one, one_mul, map_one] at this
    simp only [this]
  · have := key 1 1 (one_mem _)
    simp only [OneMemClass.coe_one, one_mul, map_one] at this
    simp only [this, Units.val_one]

theorem exists_rep_blocks (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (GL n k)] [BorelSpace (GL n k)]
    (ν : α → kˣ →* ℂˣ) (hu : ∀ a x, ‖(ν a x : ℂ)‖ = 1) (hν : ∀ a, IsUnram (ν a))
    (H : Type) [Group H] [TopologicalSpace H] :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (ρ : H × GL n k →* (V ≃ₗᵢ[ℂ] V)),
      (∀ x, IsOpen {g | ρ g x = x}) ∧
      (∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      ∃ v : V, ‖v‖ = 1 ∧ (∀ h, ∀ x ∈ KO k n, ρ (h, x) v = v) ∧
        ∃ (φ : GL n k → ℂ) (κ : Measure (GL n k)),
          (∀ (p : parab k e) x, φ (p * x) = (√(modulus k m (leviProj k e p)) : ℝ) *
            (∏ a, (ν a (GeneralLinearGroup.det (leviProj k e p a)) : ℂ)) * φ x) ∧
          (∀ x, ∀ y ∈ KO k n, φ (x * y) = φ x) ∧ φ 1 = 1 ∧ κ.IsHaarMeasure ∧ κ (KO k n) = 1 ∧
          ∀ g, inner ℂ v (ρ (1, g) v) = ∫ x in (KO k n : Set (GL n k)), φ (x * g) ∂κ := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨-, h2, h3, -, -, -, -, -, hPK⟩ := LeviInt.levi_integral_facts k α n m e
  let ψ : parab k e →* ℂˣ := (deltaHalf k m * ∏ a, ((ν a).comp GeneralLinearGroup.det).comp
    (Pi.evalMonoidHom (fun a => GL (m a) k) a)).comp (leviProj k e)
  have hψ : ∀ p, (ψ p : ℂ) = (√(modulus k m (leviProj k e p)) : ℝ) *
      (∏ a, (ν a (GeneralLinearGroup.det (leviProj k e p a)) : ℂ)) := fun p => by
    simp [ψ, val_deltaHalf, MonoidHom.finsetProd_apply]
  obtain ⟨φ, hφP, hφK, hφ1⟩ := exists_sphFn (KO k n) (parab k e) hPK ψ fun p hp => by
    ext
    rw [hψ, h3 _ (h2 p hp), Finset.prod_eq_one fun a _ => ?_]
    · simp
    · obtain ⟨g, hg⟩ := h2 p hp a
      rw [hν a, Units.val_one]
      rw [← hg]
      have h1 : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
          algebraMap 𝒪[k] k (GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
        ((algebraMap 𝒪[k] k).map_det _).symm
      exact h1.symm ▸ (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
  let K₀ : TopologicalSpace.PositiveCompacts (GL n k) :=
    ⟨⟨KO k n, SplitFlip.isCompact_KO⟩, by
      rw [SplitFlip.isOpen_KO.interior_eq]; exact ⟨1, one_mem _⟩⟩
  have hκ : Measure.haarMeasure K₀ (KO k n) = 1 := Measure.haarMeasure_self
  obtain ⟨V, _, _, ρ, hsm, hirr, v, hv1, hvK, hco⟩ := exists_rep (Measure.haarMeasure K₀) (KO k n) (parab k e)
    SplitFlip.isOpen_KO SplitFlip.isCompact_KO hκ hPK (fun p => ψ p)
    (fun p => (modulus k m (leviProj k e p) : ℂ)) (fun p => by
      rw [Complex.conj_mul', hψ, norm_mul, norm_prod, Finset.prod_eq_one fun a _ => hu a _, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← Complex.ofReal_pow,
        Real.sq_sqrt (modulus_pos k _).le]) φ hφP hφK hφ1
    (IndDual.integral_KO_mul_right k α n m e _)
  refine ⟨V, inferInstance, inferInstance, ρ.comp (MonoidHom.snd _ _), fun x => (hsm x).preimage continuous_snd,
    fun W hW => hirr W fun g => hW (1, g), v, hv1, fun _ => hvK, φ, _, fun p x => by rw [hφP, hψ], hφK, hφ1,
    inferInstance, hκ, hco⟩

end GlobalTheory.SphCyclic
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfFixedLine =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRepEqBlocks =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRepEqBlocks", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd\npublic import Mathlib.Analysis.CStarAlgebra.Module.Constructions\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleOfFixedLine\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Topology

noncomputable section

namespace GlobalTheory.SphCyclic

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix ValuativeRel

def eqBlocks (j t : ℕ) : (Σ _ : Fin j, Fin t) ≃ Fin (j * t) :=
  (Equiv.sigmaEquivProd (Fin j) (Fin t)).trans finProdFinEquiv

theorem val_eqBlocks {j t : ℕ} (a : Fin j) (s : Fin t) : (eqBlocks j t ⟨a, s⟩ : ℕ) = s + t * a := rfl

theorem eqBlocks_div {j t : ℕ} (a : Fin j) (s : Fin t) : (eqBlocks j t ⟨a, s⟩ : ℕ) / t = a := by
  rw [val_eqBlocks, Nat.add_mul_div_left _ _ s.pos, Nat.div_eq_of_lt s.2, zero_add]

theorem modExp_eqBlocks {j t : ℕ} (a : Fin j) :
    modExp (fun _ : Fin j => Fin t) a = (j * t : ℤ) - t - 2 * (a : ℕ) * t := by
  have h1 : (Finset.univ.filter fun b => a < b) = Finset.Ioi a := by ext; simp
  have h2 : (Finset.univ.filter fun b => b < a) = Finset.Iio a := by ext; simp
  rw [modExp, h1, h2, Finset.sum_const, Finset.sum_const, Fin.card_Ioi, Fin.card_Iio, Fintype.card_fin,
    nsmul_eq_mul, nsmul_eq_mul]
  have := a.2
  rw [show ((j - 1 - a : ℕ) : ℤ) = j - 1 - (a : ℕ) by omega]
  ring

theorem mem_parab_eqBlocks {R : Type} [CommRing R] {j t : ℕ} {b : GL (Fin (j * t)) R}
    (hb : ∀ x y, y < x → b.val x y = 0) : b ∈ parab R (eqBlocks j t) := by
  refine mem_parab_iff.2 fun a a' s s' h => hb _ _ ?_
  rw [Fin.lt_def, val_eqBlocks, val_eqBlocks]
  have h1 : t * (a' + 1) ≤ t * a := Nat.mul_le_mul_left _ h
  have := s'.2
  rw [mul_add, mul_one] at h1
  omega

theorem det_block {R : Type} [CommRing R] {j t : ℕ} {b : GL (Fin (j * t)) R}
    (hb : ∀ x y, y < x → b.val x y = 0) (u : Fin (j * t) → Rˣ) (hu : ∀ x, (u x : R) = b.val x x) (a : Fin j) :
    GeneralLinearGroup.det (leviProj R (eqBlocks j t) ⟨b, mem_parab_eqBlocks hb⟩ a) =
      ∏ s, u (eqBlocks j t ⟨a, s⟩) := by
  ext
  rw [GeneralLinearGroup.val_det_apply, det_of_upperTriangular, Units.coe_prod]
  · exact Finset.prod_congr rfl fun s _ => (hu _).symm
  · intro s s' h
    refine hb _ _ ?_
    rw [Fin.lt_def, val_eqBlocks, val_eqBlocks]
    exact Nat.add_lt_add_right h _

theorem exists_rep_eqBlocks (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (j t : ℕ) [MeasurableSpace (GL (Fin (j * t)) k)]
    [BorelSpace (GL (Fin (j * t)) k)] (ν : ℕ → kˣ →* ℂˣ) (hu : ∀ a x, ‖(ν a x : ℂ)‖ = 1) (hν : ∀ a, IsUnram (ν a))
    (H : Type) [Group H] [TopologicalSpace H] :
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
      (ρ : H × GL (Fin (j * t)) k →* (V ≃ₗᵢ[ℂ] V)),
      (∀ x, IsOpen {g | ρ g x = x}) ∧
      (∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      ∃ v : V, ‖v‖ = 1 ∧ (∀ h, ∀ x ∈ KO k (Fin (j * t)), ρ (h, x) v = v) ∧
        ∃ (φ : GL (Fin (j * t)) k → ℂ) (κ : Measure (GL (Fin (j * t)) k)),
          (∀ (b : GL (Fin (j * t)) k) (u : Fin (j * t) → kˣ), (∀ x y, y < x → b.val x y = 0) →
            (∀ x, (u x : k) = b.val x x) → ∀ g, φ (b * g) = (∏ x : Fin (j * t), (ν (x / t) (u x) : ℂ) *
              (nabs k (u x) ^ ((((j * t : ℕ) : ℝ) - t) / 2 - ((x / t : ℕ) : ℝ) * t) : ℝ)) * φ g) ∧
          (∀ x, ∀ y ∈ KO k (Fin (j * t)), φ (x * y) = φ x) ∧ φ 1 = 1 ∧ κ.IsHaarMeasure ∧
          κ (KO k (Fin (j * t))) = 1 ∧
          ∀ g, inner ℂ v (ρ (1, g) v) = ∫ x in (KO k (Fin (j * t)) : Set (GL (Fin (j * t)) k)), φ (x * g) ∂κ := by
  obtain ⟨V, _, _, ρ, h1, h2, v, h3, h4, φ, κ, h5, h6⟩ :=
    exists_rep_blocks k (eqBlocks j t) (fun a => ν a) (fun a => hu a) (fun a => hν a) H
  refine ⟨V, inferInstance, inferInstance, ρ, h1, h2, v, h3, h4, φ, κ, fun b u hb hbu g => ?_, h6⟩
  rw [h5 ⟨b, mem_parab_eqBlocks hb⟩ g, ← val_deltaHalf, deltaHalf_apply, Units.coe_prod, ← Finset.prod_mul_distrib,
    ← (eqBlocks j t).prod_comp, Fintype.prod_sigma]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [det_block hb u hbu, map_prod, map_prod, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [eqBlocks_div, mul_comm, ← val_absPow_ofReal, modExp_eqBlocks]
  congr 3
  push_cast
  ring

end GlobalTheory.SphCyclic
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRepEqBlocks =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM", "h": "module\n\npublic import Formalism.LocalToGlobal.Divisibility.QLocTied\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaHalfMulUnrTorus\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRepEqBlocks\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.SphCyclic

variable {L : Type} [Field L] [NumberField L] {P : HeightOneSpectrum (𝓞 L)}

theorem nrm_eq {nrm : AbsoluteValue (P.adicCompletion L) ℝ} (h : IsNrm P nrm) (x : (P.adicCompletion L)ˣ) :
    nrm x = (qP P : ℝ) ^ (WithZero.log (Valued.v (x : P.adicCompletion L))) := by
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective L P (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  set m := WithZero.log (Valued.v (x : P.adicCompletion L)) with hm
  have hx : Valued.v (x : P.adicCompletion L) = WithZero.exp m := (WithZero.exp_log (by simp)).symm
  have h1 : nrm π = (qP P : ℝ)⁻¹ := (h (Units.mk0 π hπ0)).2 hπ
  have h2 := (h (x * (Units.mk0 π hπ0) ^ m)).1 (by
    show Valued.v ((x * (Units.mk0 π hπ0) ^ m : (P.adicCompletion L)ˣ) : P.adicCompletion L) = 1
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0,
      hπ, hx, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp)
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0, h1, _root_.inv_zpow] at h2
  exact eq_of_div_eq_one h2

theorem exists_isUnrM : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (nrm : AbsoluteValue (P.adicCompletion L) ℝ), IsNrm P nrm → ∀ (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsNu P (ν i)) → ∀ r t j : ℕ, 1 ≤ t → ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (ρ : GL (Fin r) (P.adicCompletion L) × GL (Fin (j * t)) (P.adicCompletion L) →* (V ≃ₗᵢ[ℂ] V)), IsUnrM (OP P) nrm r (j * t) (satC nrm ν t (j * t)) ρ := by
  intro L _ _ P nrm hn ν hν r t j _
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (P.adicCompletion L))
    (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hK : GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (j * t)) = GLint (OP P) (j * t) := by
    ext g
    rw [GlobalTheory.SplitFlip.mem_KO_iff]
    simp only [he.le_one_iff_le_one, Valuation.mem_integer_iff]
    exact Iff.rfl
  obtain ⟨V, _, _, ρ, h1, h2, v, h3, h4, φ, κ, h5, h6, h7, h8, h9, h10⟩ :=
    @exists_rep_eqBlocks (P.adicCompletion L) _ _ _ _ j t (instMeasGL _) (instBorelGL _) (fun a => ν (a + 1))
      (fun a => (hν _).unitary) (fun a x hx => (hν _).unr x (he.eq_one_iff_eq_one.1 hx))
      (GL (Fin r) (P.adicCompletion L)) _ _
  rw [hK] at h4 h6 h9 h10
  refine ⟨V, inferInstance, inferInstance, ρ, h1, h2, v, h3, fun k₁ _ => h4 k₁, φ, κ, fun b hb k hk => ?_,
    h8.toIsMulLeftInvariant, h9, h10⟩
  have hd : ∀ x, b.val x x ≠ 0 := by
    have := b.det_ne_zero
    rw [det_of_upperTriangular hb] at this
    exact fun x => Finset.prod_ne_zero_iff.1 this x (Finset.mem_univ _)
  have h11 := h5 b (fun x => Units.mk0 _ (hd x)) (fun x y h => hb h) (fun _ => rfl) 1
  rw [mul_one, h7, mul_one] at h11
  rw [h6 b k hk, h11]
  refine Finset.prod_congr rfl fun x _ => ?_
  have h12 : GlobalTheory.SplitWeil.nabs (P.adicCompletion L) (Units.mk0 _ (hd x)) = nrm (b.val x x) :=
    (GlobalTheory.LGrp.BorelCompletion.nabs_completion P _).trans (nrm_eq hn (Units.mk0 _ (hd x))).symm
  rw [h12, satC, chi0, dite_eq_right (hd x), mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (nrm.pos (hd x))]
  congr 3
  have : ((x : ℕ) : ℝ) = (((x : ℕ) % t : ℕ) : ℝ) + (((x : ℕ) / t : ℕ) : ℝ) * t := by
    exact_mod_cast (Nat.mod_add_div' (x : ℕ) t).symm
  linarith

end GlobalTheory.SphCyclic
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIsCompactParahoricGLCompletion =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIsCompactParahoricGLCompletion", "h": "module\n\npublic import Formalism.LocalToGlobal.Divisibility.QLocTied\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ParahoricTopo

theorem isClopen_OP {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) :
    IsClopen ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) :=
  Valued.isClopen_valuationSubring (P.adicCompletion L)

theorem isClopen_mulSet {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
    (ϖ : P.adicCompletion L) (hϖ : ϖ ≠ 0) :
    IsClopen {y : P.adicCompletion L | ∃ o ∈ OP P, y = ϖ * o} := by
  have e : {y : P.adicCompletion L | ∃ o ∈ OP P, y = ϖ * o} =
      (fun y => ϖ⁻¹ * y) ⁻¹' ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨o, ho, rfl⟩
      rwa [← mul_assoc, inv_mul_cancel₀ hϖ, one_mul]
    · intro h
      exact ⟨_, h, by rw [← mul_assoc, mul_inv_cancel₀ hϖ, one_mul]⟩
  rw [e]
  exact (isClopen_OP P).preimage (continuous_const.mul continuous_id)

theorem isOpen_isCompact_parJ : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ), IsOpen (parJ (OP P) (piP P : P.adicCompletion L) r c) ∧ IsCompact (parJ (OP P) (piP P : P.adicCompletion L) r c) := by
  intro L _ _ P r c
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (P.adicCompletion L))
    (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hK : GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (r + c)) = GLint (OP P) (r + c) := by
    ext g
    rw [GlobalTheory.SplitFlip.mem_KO_iff]
    simp only [he.le_one_iff_le_one, Valuation.mem_integer_iff]
    exact Iff.rfl
  have hS := isClopen_mulSet P (piP P : P.adicCompletion L) (Units.ne_zero _)
  set B : Set (GL (Fin (r + c)) (P.adicCompletion L)) :=
    {k | bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) ∈
      IIset (t := c) (a := r) (OP P) (piP P : P.adicCompletion L)} with hB
  have hBe : B = ⋂ i : Fin c, ⋂ j : Fin r,
      (fun k : GL (Fin (r + c)) (P.adicCompletion L) =>
        (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j)) ⁻¹'
        {y : P.adicCompletion L | ∃ o ∈ OP P, y = (piP P : P.adicCompletion L) * o} := by
    ext k
    simp only [hB, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, IIset, bDA, Matrix.submatrix_apply]
  have hcont : ∀ (i : Fin (r + c)) (j : Fin (r + c)), Continuous fun k : GL (Fin (r + c)) (P.adicCompletion L) =>
      (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) i j := fun i j =>
    (Units.continuous_val (M := Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).matrix_elem i j
  have hBc : IsClopen B := by
    rw [hBe]
    exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => hS.preimage (hcont _ _)
  have hP : parJ (OP P) (piP P : P.adicCompletion L) r c =
      (GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (r + c)) : Set _) ∩ B := by
    rw [hK]; rfl
  rw [hP]
  exact ⟨GlobalTheory.SplitFlip.isOpen_KO.inter hBc.isOpen, GlobalTheory.SplitFlip.isCompact_KO.inter_right hBc.isClosed⟩

end GlobalTheory.ParahoricTopo
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIsCompactParahoricGLCompletion =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTame =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTame", "h": "module\n\npublic import Formalism.LocalToGlobal.Divisibility.QLocTied\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem.LamMul

section Blocks

variable {S : Type*} [CommRing S] {r c : ℕ}

theorem det_eq_of_lower_zero (M : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (h : M.submatrix (Fin.natAdd r) (Fin.castAdd c) = 0) :
    M.det = (M.submatrix (Fin.castAdd c) (Fin.castAdd c)).det * (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
  have e : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (M.submatrix (Fin.castAdd c) (Fin.castAdd c)) (M.submatrix (Fin.castAdd c) (Fin.natAdd r)) 0
        (M.submatrix (Fin.natAdd r) (Fin.natAdd r)) := by
    rw [← h]
    ext (i | i) (j | j) <;> simp
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, e, Matrix.det_fromBlocks_zero₂₁]

theorem mul_dd_of_lower_zero (M N : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (h : M.submatrix (Fin.natAdd r) (Fin.castAdd c) = 0) :
    (M * N).submatrix (Fin.natAdd r) (Fin.natAdd r) =
      M.submatrix (Fin.natAdd r) (Fin.natAdd r) * N.submatrix (Fin.natAdd r) (Fin.natAdd r) := by
  ext i j
  have h0 : ∀ a, M (Fin.natAdd r i) (Fin.castAdd c a) = 0 := fun a => congrFun (congrFun h i) a
  simp [Matrix.mul_apply, Fin.sum_univ_add, h0]

theorem dd_mod (I : Ideal S) (K K' : Matrix (Fin (r + c)) (Fin (r + c)) S)
    (hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) (hK' : ∀ i j, K' (Fin.natAdd r i) (Fin.castAdd c j) ∈ I)
    (hu : IsUnit K.det) (hu' : IsUnit K'.det) :
    IsUnit (Ideal.Quotient.mk I (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ∧
    IsUnit (Ideal.Quotient.mk I (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) ∧
    ((K * K').submatrix (Fin.natAdd r) (Fin.natAdd r)).det -
      (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det * (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ∈ I := by
  have key : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, (∀ i j, X (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) →
      ((Ideal.Quotient.mk I).mapMatrix X).submatrix (Fin.natAdd r) (Fin.castAdd c) = 0 := by
    intro X hX
    ext i j
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hX i j
  have sub : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, Ideal.Quotient.mk I (X.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
      (((Ideal.Quotient.mk I).mapMatrix X).submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    intro X
    rw [RingHom.map_det]
    rfl
  have unit : ∀ X : Matrix (Fin (r + c)) (Fin (r + c)) S, (∀ i j, X (Fin.natAdd r i) (Fin.castAdd c j) ∈ I) →
      IsUnit X.det → IsUnit (Ideal.Quotient.mk I (X.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) := by
    intro X hX hu
    have h1 : IsUnit ((Ideal.Quotient.mk I).mapMatrix X).det := by
      rw [← RingHom.map_det]
      exact hu.map _
    rw [det_eq_of_lower_zero _ (key X hX)] at h1
    rw [sub]
    exact isUnit_of_mul_isUnit_right h1
  refine ⟨unit K hK hu, unit K' hK' hu', ?_⟩
  rw [← Ideal.Quotient.eq, map_mul, sub, sub, sub, map_mul,
    mul_dd_of_lower_zero _ _ (key K hK), Matrix.det_mul]

end Blocks

section Val

variable {F Γ : Type} [Field F] [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ) (O : Subring F) (ε : Γ)

def redI (hO : ∀ x ∈ O, v x ≤ 1) : Ideal O where
  carrier := {a | v (a : F) ≤ ε}
  add_mem' {a b} ha hb := by
    show v ((a : F) + b) ≤ ε
    exact (v.map_add _ _).trans (max_le ha hb)
  zero_mem' := by
    show v ((0 : O) : F) ≤ ε
    simp
  smul_mem' a b hb := by
    show v ((a : F) * b) ≤ ε
    rw [map_mul]
    exact (mul_le_of_le_one_left' (hO _ a.2)).trans hb

variable {v O ε}

theorem val_eq_one_of_isUnit (hO : ∀ x ∈ O, v x ≤ 1) (hε : ε < 1) (a : O)
    (h : IsUnit (Ideal.Quotient.mk (redI v O ε hO) a)) : v (a : F) = 1 := by
  obtain ⟨b, hb⟩ := h.exists_right_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 : a * b - 1 ∈ redI v O ε hO := by
    apply Ideal.Quotient.eq.1
    simpa using hb
  have h2 : v ((a : F) * b - 1) ≤ ε := by
    have h1' : v (((a * b - 1 : O)) : F) ≤ ε := h1
    simpa using h1'
  have h3 : v ((a : F) * b) = 1 := by
    have e : (a : F) * b = ((a : F) * b - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · simp
    · simpa using h2.trans_lt hε
  rw [map_mul] at h3
  refine le_antisymm (hO _ a.2) ?_
  rw [← h3]
  exact mul_le_of_le_one_right' (hO _ b.2)


omit [LinearOrderedCommGroupWithZero Γ] in
theorem exists_lift {n : ℕ} {k : GL (Fin n) F} (hk : k ∈ GLint O n) :
    ∃ K : Matrix (Fin n) (Fin n) O, (k : Matrix (Fin n) (Fin n) F) = K.map O.subtype ∧ IsUnit K.det := by
  let K : Matrix (Fin n) (Fin n) O := fun i j => ⟨(k : Matrix (Fin n) (Fin n) F) i j, hk.1 i j⟩
  let K' : Matrix (Fin n) (Fin n) O := fun i j => ⟨((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, hk.2 i j⟩
  have e : (k : Matrix (Fin n) (Fin n) F) = K.map O.subtype := by ext i j; rfl
  have e' : ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = K'.map O.subtype := by ext i j; rfl
  refine ⟨K, e, Matrix.isUnit_det_of_right_inverse (B := K') ?_⟩
  apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
  show (K * K').map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
  rw [Matrix.map_mul, ← e, ← e', ← Units.val_mul, mul_inv_cancel, Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

omit [LinearOrderedCommGroupWithZero Γ] in
theorem det_dd_map {r c : ℕ} (K : Matrix (Fin (r + c)) (Fin (r + c)) O) :
    (bDD (K.map O.subtype)).det = (((K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : O) : F) := by
  show _ = O.subtype _
  rw [RingHom.map_det]
  rfl

theorem dd_val (hO : ∀ x ∈ O, v x ≤ 1) (hε : ε < 1) {r c : ℕ} {k k' : GL (Fin (r + c)) F}
    (hk : k ∈ GLint O (r + c)) (hk' : k' ∈ GLint O (r + c))
    (hd : ∀ i j, v ((k : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ≤ ε)
    (hd' : ∀ i j, v ((k' : Matrix (Fin (r + c)) (Fin (r + c)) F) (Fin.natAdd r i) (Fin.castAdd c j)) ≤ ε) :
    v (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    v (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) F)).det = 1 ∧
    v ((bDD ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F)).det -
      (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) F)).det) ≤ ε := by
  obtain ⟨K, e, hu⟩ := exists_lift hk
  obtain ⟨K', e', hu'⟩ := exists_lift hk'
  have hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) ∈ redI v O ε hO := fun i j => by
    have := hd i j
    rw [e] at this
    exact this
  have hK' : ∀ i j, K' (Fin.natAdd r i) (Fin.castAdd c j) ∈ redI v O ε hO := fun i j => by
    have := hd' i j
    rw [e'] at this
    exact this
  obtain ⟨h1, h2, h3⟩ := dd_mod (redI v O ε hO) K K' hK hK' hu hu'
  have em : ((k * k' : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = (K * K').map O.subtype := by
    rw [Units.val_mul, e, e', Matrix.map_mul]
  rw [em, e, e', det_dd_map, det_dd_map, det_dd_map]
  refine ⟨val_eq_one_of_isUnit hO hε _ h1, val_eq_one_of_isUnit hO hε _ h2, ?_⟩
  have h3' : v (((((K * K').submatrix (Fin.natAdd r) (Fin.natAdd r)).det -
      (K.submatrix (Fin.natAdd r) (Fin.natAdd r)).det * (K'.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : O)) : F) ≤ ε := h3
  simpa using h3'

end Val

section Main

theorem lamJ_mul : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (δ : (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) (P.adicCompletion L)), k ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → k' ∈ parJ (OP P) (piP P : P.adicCompletion L) r c → lamJ δ (k * k') = lamJ δ k * lamJ δ k' := by
  intro L _ _ P δ hδ r c k k' hk hk'
  have hO : ∀ x ∈ OP P, Valued.v x ≤ 1 := fun x hx => hx
  have hε : (WithZero.exp (-1 : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπ : Valued.v (piP P : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec P
  have small : ∀ {g : GL (Fin (r + c)) (P.adicCompletion L)}, g ∈ parJ (OP P) (piP P : P.adicCompletion L) r c →
      ∀ i j, Valued.v ((g : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j)) ≤
        WithZero.exp (-1 : ℤ) := by
    intro g hg i j
    obtain ⟨o, ho, e⟩ := hg.2 i j
    have e' : (g : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j) =
        (piP P : P.adicCompletion L) * o := e
    rw [e', map_mul, hπ]
    exact mul_le_of_le_one_right' (hO _ ho)
  obtain ⟨ha, hb, hxy⟩ := dd_val hO hε hk.1 hk'.1 (small hk) (small hk')
  unfold lamJ
  set a := (bDD (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hadef
  set b := (bDD (k' : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hbdef
  set x := (bDD ((k * k' : GL (Fin (r + c)) (P.adicCompletion L)) : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det with hxdef
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hab : Valued.v (a * b) = 1 := by rw [map_mul, ha, hb, one_mul]
  have hx : Valued.v x = 1 := by
    have e : x = (x - a * b) + a * b := by ring
    rw [e, Valuation.map_add_eq_of_lt_right, hab]
    rw [hab]
    exact hxy.trans_lt hε
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  have tame := hδ.tame (Units.mk0 x hx0 * (Units.mk0 a ha0 * Units.mk0 b hb0)⁻¹) (by
    show Valued.v _ = 1
    simp [hx, ha, hb]) (by
    have e : x * (a * b)⁻¹ - 1 = (x - a * b) * (a * b)⁻¹ := by field_simp
    simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
    rw [e, map_mul, map_inv₀, hab, inv_one, mul_one]
    exact hxy)
  rw [map_mul, map_inv, mul_inv_eq_one, map_mul] at tame
  simp only [chi0, dif_neg hx0, dif_neg ha0, dif_neg hb0, tame, Units.val_mul]

end Main

end GlobalTheory.Mem.LamMul
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTame =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricTypeRCMulInvMem =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricTypeRCMulInvMem", "h": "module\n\npublic import Formalism.LocalToGlobal.Divisibility.QLocTied\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ParGroup

variable {F : Type} [Field F] (O : Subring F) (ϖ : F)

def InW (x : F) : Prop := ∃ o ∈ O, x = ϖ * o

theorem inW_sum {ι : Type} (s : Finset ι) (f : ι → F) (h : ∀ i ∈ s, InW O ϖ (f i)) :
    InW O ϖ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, O.zero_mem, by simp⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    obtain ⟨o₁, ho₁, e₁⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨o₂, ho₂, e₂⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact ⟨o₁ + o₂, O.add_mem ho₁ ho₂, by rw [e₁, e₂, mul_add]⟩

theorem inW_mul_right {x a : F} (hx : InW O ϖ x) (ha : a ∈ O) : InW O ϖ (x * a) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨o * a, O.mul_mem ho ha, by ring⟩

theorem inW_mul_left {x a : F} (ha : a ∈ O) (hx : InW O ϖ x) : InW O ϖ (a * x) := by
  obtain ⟨o, ho, rfl⟩ := hx
  exact ⟨a * o, O.mul_mem ha ho, by ring⟩

theorem mul_mem_parJ {r c : ℕ} {k k' : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c)
    (hk' : k' ∈ parJ O ϖ r c) : k * k' ∈ parJ O ϖ r c := by
  obtain ⟨hkG, hkW⟩ := hk
  obtain ⟨hkG', hkW'⟩ := hk'
  refine ⟨(GLint O (r + c)).mul_mem hkG hkG', ?_⟩
  have hI : IsInt O (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.1
  have hI' : IsInt O (k' : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG'.1
  intro i j
  show InW O ϖ _
  simp only [bDA, Matrix.submatrix_apply, Units.val_mul, Matrix.mul_apply]
  apply inW_sum
  intro l _
  refine Fin.addCases (fun l => ?_) (fun l => ?_) l
  · exact inW_mul_right O ϖ (hkW i l) (hI' _ _)
  · exact inW_mul_left O ϖ (hI _ _) (hkW' l j)
private theorem lower_block_eq_zero_of_mul_eq_one {R : Type} [CommRing R] {r c : ℕ}
    (K N : Matrix (Fin (r + c)) (Fin (r + c)) R) (hKN : K * N = 1)
    (hK : ∀ i j, K (Fin.natAdd r i) (Fin.castAdd c j) = 0) (i : Fin c) (j : Fin r) :
    N (Fin.natAdd r i) (Fin.castAdd c j) = 0 := by
  let D : Matrix (Fin c) (Fin c) R := K.submatrix (Fin.natAdd r) (Fin.natAdd r)
  let T : Matrix (Fin c) (Fin c) R := N.submatrix (Fin.natAdd r) (Fin.natAdd r)
  let S : Matrix (Fin c) (Fin r) R := N.submatrix (Fin.natAdd r) (Fin.castAdd c)
  have key : ∀ a b, (K * N) (Fin.natAdd r a) b =
      ∑ l : Fin c, K (Fin.natAdd r a) (Fin.natAdd r l) * N (Fin.natAdd r l) b := by
    intro a b
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    simp [hK]
  have hDT : D * T = 1 := by
    ext a b
    have h := key a (Fin.natAdd r b)
    rw [hKN] at h
    simp only [D, T, Matrix.mul_apply, Matrix.submatrix_apply]
    rw [← h]
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : Fin.natAdd r a ≠ Fin.natAdd r b := by
        intro e
        apply hab
        ext
        have := congrArg Fin.val e
        simp at this
        omega
      rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hab]
  have hDS : D * S = 0 := by
    ext a b
    have h := key a (Fin.castAdd c b)
    rw [hKN] at h
    have hne : Fin.natAdd r a ≠ Fin.castAdd c b := by
      intro e
      have := congrArg Fin.val e
      have hb := b.isLt
      simp at this
      omega
    rw [Matrix.one_apply_ne hne] at h
    simp only [D, S, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.zero_apply]
    exact h.symm
  have hTD : T * D = 1 := by
    first
    | exact mul_eq_one_comm.mp hDT
    | rw [← Matrix.inv_eq_right_inv hDT]
      exact Matrix.nonsing_inv_mul D (Matrix.isUnit_det_of_right_inverse hDT)
  have hS : S = 0 := by
    calc S = (T * D) * S := by rw [hTD, Matrix.one_mul]
      _ = T * (D * S) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hDS, Matrix.mul_zero]
  exact congrFun (congrFun hS i) j

theorem inv_mem_parJ {r c : ℕ} {k : GL (Fin (r + c)) F} (hϖ : ϖ ∈ O) (hk : k ∈ parJ O ϖ r c) :
    k⁻¹ ∈ parJ O ϖ r c := by
  obtain ⟨hkG, hkW⟩ := hk
  refine ⟨(GLint O (r + c)).inv_mem hkG, ?_⟩
  have hI : IsInt O (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.1
  have hJ : IsInt O ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) := hkG.2
  let KO : Matrix (Fin (r + c)) (Fin (r + c)) O := fun a b => ⟨(k : Matrix (Fin (r + c)) (Fin (r + c)) F) a b, hI a b⟩
  let NO : Matrix (Fin (r + c)) (Fin (r + c)) O :=
    fun a b => ⟨((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) a b, hJ a b⟩
  have hKN : KO * NO = 1 := by
    apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have e1 : KO.map O.subtype = (k : Matrix (Fin (r + c)) (Fin (r + c)) F) := by ext; rfl
    have e2 : NO.map O.subtype = ((k⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) := by ext; rfl
    rw [e1, e2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let π := Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)})
  have hKNb : KO.map π * NO.map π = 1 := by
    rw [← Matrix.map_mul, hKN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hK0 : ∀ i j, KO.map π (Fin.natAdd r i) (Fin.castAdd c j) = 0 := by
    intro i j
    obtain ⟨o, ho, e⟩ := hkW i j
    rw [Matrix.map_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    simp only [bDA, Matrix.submatrix_apply] at e
    simp only [KO, Subring.coe_mul, e]
    ring
  intro i j
  have h0 := lower_block_eq_zero_of_mul_eq_one (KO.map π) (NO.map π) hKNb hK0 i j
  rw [Matrix.map_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
  obtain ⟨⟨o, ho⟩, e⟩ := h0
  refine ⟨o, ho, ?_⟩
  have e' := congrArg Subtype.val e
  simp only [NO, Subring.coe_mul] at e'
  simp only [bDA, Matrix.submatrix_apply]
  rw [← e']
  ring

theorem parJ_mul_inv : ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F), ϖ ∈ O → ∀ (r c : ℕ) (k k' : GL (Fin (r + c)) F),
    k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c → k * k' ∈ parJ O ϖ r c ∧ k⁻¹ ∈ parJ O ϖ r c := by
  intro F _ O ϖ hϖ r c k k' hk hk'
  exact ⟨mul_mem_parJ O ϖ hk hk', inv_mem_parJ O ϖ hϖ hk⟩

end GlobalTheory.ParGroup
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricTypeRCMulInvMem =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOne =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOne", "h": "module\n\npublic import Formalism.LocalToGlobal.Divisibility.QLocTied\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockUpperTriangularGLMulDetInv\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIsCompactParahoricGLCompletion\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricCharacterMulOfTame\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParahoricTypeRCMulInvMem\nimport Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section
namespace GlobalTheory.TypeStep

section Gen

variable {F : Type} [Field F] {r c : ℕ}

theorem bDA_mul {p q : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    bDA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 :=
  (_root_.GlobalTheory.HQStepBlocks.main F r c p q hp hq).1

theorem bAA_mul {p q : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    bAA ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) =
      bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bAA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) :=
  (_root_.GlobalTheory.HQStepBlocks.main F r c p q hp hq).2.1

theorem bDD_mul {p q : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    bDD ((p * q : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) =
      bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) * bDD (q : Matrix (Fin (r + c)) (Fin (r + c)) F) :=
  (_root_.GlobalTheory.HQStepBlocks.main F r c p q hp hq).2.2.1

theorem det_blocks {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (p : Matrix (Fin (r + c)) (Fin (r + c)) F).det =
      (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det * (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det :=
  (_root_.GlobalTheory.HQStepBlocks.main F r c p p hp hp).2.2.2.1

theorem bDA_inv {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    bDA ((p⁻¹ : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 :=
  (_root_.GlobalTheory.HQStepBlocks.main F r c p p hp hp).2.2.2.2

theorem detA_ne {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 := fun h =>
  p.det_ne_zero (by rw [det_blocks hp, h, zero_mul])

theorem detD_ne {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 := fun h =>
  p.det_ne_zero (by rw [det_blocks hp, h, mul_zero])

theorem bDA_one : bDA ((1 : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
  ext i j
  simp [bDA, Matrix.one_apply, Fin.ext_iff]
  omega

def levA (p : GL (Fin (r + c)) F) : GL (Fin r) F :=
  open Classical in
  if h : (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 then GeneralLinearGroup.mkOfDetNeZero _ h else 1

def levD (p : GL (Fin (r + c)) F) : GL (Fin c) F :=
  open Classical in
  if h : (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ≠ 0 then GeneralLinearGroup.mkOfDetNeZero _ h else 1

theorem levA_val {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (levA p : Matrix (Fin r) (Fin r) F) = bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) := by
  rw [levA, dite_eq_left (detA_ne hp)]; rfl

theorem levD_val {p : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (levD p : Matrix (Fin c) (Fin c) F) = bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F) := by
  rw [levD, dite_eq_left (detD_ne hp)]; rfl

theorem lev_mul {p q : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    ((levA (p * q), levD (p * q)) : GL (Fin r) F × GL (Fin c) F) = (levA p, levD p) * (levA q, levD q) := by
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · simp only [Prod.fst_mul, Units.val_mul]
    rw [levA_val (bDA_mul hp hq), levA_val hp, levA_val hq, bAA_mul hp hq]
  · simp only [Prod.snd_mul, Units.val_mul]
    rw [levD_val (bDA_mul hp hq), levD_val hp, levD_val hq, bDD_mul hp hq]

theorem unitCharExtendedByZero_mul (δ : Fˣ →* ℂˣ) (x y : F) : chi0 δ (x * y) = chi0 δ x * chi0 δ y := by
  by_cases hx : x = 0
  · simp [chi0, hx]
  by_cases hy : y = 0
  · simp [chi0, hy]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  simp only [chi0, dif_neg hx, dif_neg hy, dif_neg hxy]
  rw [← Units.val_mul, ← map_mul]
  congr 3
  ext; simp

def chiP (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ) (p : GL (Fin (r + c)) F) : ℂ :=
  ((nrm (bAA (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ^ ((c : ℝ) / 2) *
    nrm (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det ^ (-(r : ℝ) / 2) : ℝ) : ℂ) *
    chi0 δ (bDD (p : Matrix (Fin (r + c)) (Fin (r + c)) F)).det

theorem chiP_mul (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ) {p q : GL (Fin (r + c)) F}
    (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    chiP nrm δ (p * q) = chiP nrm δ p * chiP nrm δ q := by
  unfold chiP
  rw [bAA_mul hp hq, bDD_mul hp hq, det_mul, det_mul, map_mul, map_mul, unitCharExtendedByZero_mul,
    Real.mul_rpow (nrm.nonneg _) (nrm.nonneg _), Real.mul_rpow (nrm.nonneg _) (nrm.nonneg _)]
  push_cast
  ring

end Gen

section Constr

variable {F : Type} [Field F] (O : Subring F) (ϖ : F) (nrm : AbsoluteValue F ℝ) (δ : Fˣ →* ℂˣ) {r c : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (ρ : GL (Fin r) F × GL (Fin c) F →* (V ≃ₗᵢ[ℂ] V)) (v₀ : V)

def PJset (r c : ℕ) : Set (GL (Fin (r + c)) F) :=
  {g | ∃ p : GL (Fin (r + c)) F, bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 ∧ ∃ k ∈ parJ O ϖ r c, g = p * k}

def fvec (g : GL (Fin (r + c)) F) : V :=
  open Classical in
  if h : g ∈ PJset O ϖ r c then
    (chiP nrm δ h.choose * lamJ δ h.choose_spec.2.choose) • ρ (levA h.choose, levD h.choose) v₀
  else 0

variable {O ϖ nrm δ ρ v₀}

theorem cons (hgrp : ∀ k k' : GL (Fin (r + c)) F, k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c →
      k * k' ∈ parJ O ϖ r c ∧ k⁻¹ ∈ parJ O ϖ r c)
    (hlam : ∀ k k' : GL (Fin (r + c)) F, k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c →
      lamJ δ (k * k') = lamJ δ k * lamJ δ k')
    (hfix : ∀ q : GL (Fin (r + c)) F, q ∈ parJ O ϖ r c → bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 →
      ρ (levA q, levD q) v₀ = v₀ ∧ chiP nrm δ q = lamJ δ q)
    {p p' k k' : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hp' : bDA (p' : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) (hk : k ∈ parJ O ϖ r c) (hk' : k' ∈ parJ O ϖ r c)
    (e : p * k = p' * k') :
    (chiP nrm δ p * lamJ δ k) • ρ (levA p, levD p) v₀ = (chiP nrm δ p' * lamJ δ k') • ρ (levA p', levD p') v₀ := by
  obtain ⟨q, rfl⟩ : ∃ q, p = p' * q := ⟨p'⁻¹ * p, by simp⟩
  have hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 := by
    have := bDA_mul (bDA_inv hp') hp
    simpa using this
  have hkq : k' = q * k := (mul_left_cancel (a := p') (by rw [← mul_assoc]; exact e)).symm
  have hqJ : q ∈ parJ O ϖ r c := by
    have : q = k' * k⁻¹ := by rw [hkq]; simp
    rw [this]
    exact (hgrp _ _ hk' (hgrp _ _ hk hk).2).1
  obtain ⟨h1, h2⟩ := hfix q hqJ hq
  rw [chiP_mul nrm δ hp' hq, lev_mul hp' hq, hkq, hlam _ _ hqJ hk, map_mul]
  show (chiP nrm δ p' * chiP nrm δ q * lamJ δ k) • (ρ (levA p', levD p')) ((ρ (levA q, levD q)) v₀) = _
  rw [h1, h2, mul_assoc]

end Constr

section Mem

variable {F : Type} [Field F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {δ : Fˣ →* ℂˣ} {r c : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ρ : GL (Fin r) F × GL (Fin c) F →* (V ≃ₗᵢ[ℂ] V)} {v₀ : V}
  (hgrp : ∀ k k' : GL (Fin (r + c)) F, k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c →
      k * k' ∈ parJ O ϖ r c ∧ k⁻¹ ∈ parJ O ϖ r c)
  (hlam : ∀ k k' : GL (Fin (r + c)) F, k ∈ parJ O ϖ r c → k' ∈ parJ O ϖ r c →
      lamJ δ (k * k') = lamJ δ k * lamJ δ k')
  (hfix : ∀ q : GL (Fin (r + c)) F, q ∈ parJ O ϖ r c → bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0 →
      ρ (levA q, levD q) v₀ = v₀ ∧ chiP nrm δ q = lamJ δ q)

include hgrp hlam hfix in
theorem fvec_eq {p k : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0)
    (hk : k ∈ parJ O ϖ r c) :
    fvec O ϖ nrm δ ρ v₀ (p * k) = (chiP nrm δ p * lamJ δ k) • ρ (levA p, levD p) v₀ := by
  have h : p * k ∈ PJset O ϖ r c := ⟨p, hp, k, hk, rfl⟩
  rw [fvec, dite_eq_left h]
  have h2 := h.choose_spec.2.choose_spec.1
  have h3 := h.choose_spec.2.choose_spec.2
  exact cons hgrp hlam hfix h.choose_spec.1 hp h2 hk h3.symm

include hgrp in
theorem fvec_out {g : GL (Fin (r + c)) F} (hg : g ∉ PJset O ϖ r c) : fvec O ϖ nrm δ ρ v₀ g = 0 := by
  rw [fvec, dif_neg hg]

include hgrp in
theorem mul_mem_PJ_iff {p g : GL (Fin (r + c)) F} (hp : bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    p * g ∈ PJset O ϖ r c ↔ g ∈ PJset O ϖ r c := by
  constructor
  · rintro ⟨p₁, hp₁, k₁, hk₁, e⟩
    refine ⟨p⁻¹ * p₁, bDA_mul (bDA_inv hp) hp₁, k₁, hk₁, ?_⟩
    rw [mul_assoc, ← e]; simp
  · rintro ⟨p₁, hp₁, k₁, hk₁, rfl⟩
    exact ⟨p * p₁, bDA_mul hp hp₁, k₁, hk₁, by rw [mul_assoc]⟩

include hgrp in
theorem mul_mem_PJ_iff' {k g : GL (Fin (r + c)) F} (hk : k ∈ parJ O ϖ r c) :
    g * k ∈ PJset O ϖ r c ↔ g ∈ PJset O ϖ r c := by
  constructor
  · rintro ⟨p₁, hp₁, k₁, hk₁, e⟩
    refine ⟨p₁, hp₁, k₁ * k⁻¹, (hgrp _ _ hk₁ (hgrp _ _ hk hk).2).1, ?_⟩
    rw [← mul_assoc, ← e]; simp
  · rintro ⟨p₁, hp₁, k₁, hk₁, rfl⟩
    exact ⟨p₁, hp₁, k₁ * k, (hgrp _ _ hk₁ hk).1, by rw [mul_assoc]⟩

theorem unitCharExtendedByZero_det_eq_char_det (m : GL (Fin c) F) :
    chi0 δ (m : Matrix (Fin c) (Fin c) F).det = ((δ (Matrix.GeneralLinearGroup.det m) : ℂˣ) : ℂ) := by
  have h : (m : Matrix (Fin c) (Fin c) F).det ≠ 0 := m.det_ne_zero
  rw [chi0, dif_neg h]
  congr 2
  exact Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply])

include hgrp hlam hfix in
theorem fvec_mem : fvec O ϖ nrm δ ρ v₀ ∈ typeSp O ϖ nrm δ r c ρ := by
  refine ⟨fun p m₁ m₂ hp h1 h2 g => ?_, fun k hk g => ?_⟩
  · have e1 : m₁ = levA p := Units.ext ((levA_val hp).trans h1).symm
    have e2 : m₂ = levD p := Units.ext ((levD_val hp).trans h2).symm
    have hs : (((nrm (m₁ : Matrix (Fin r) (Fin r) F).det ^ ((c : ℝ) / 2) *
          nrm (m₂ : Matrix (Fin c) (Fin c) F).det ^ (-(r : ℝ) / 2) : ℝ) : ℂ) *
        ((δ (Matrix.GeneralLinearGroup.det m₂) : ℂˣ) : ℂ)) = chiP nrm δ p := by
      rw [chiP, ← unitCharExtendedByZero_det_eq_char_det, h1, h2]
    rw [hs, e1, e2]
    by_cases hg : g ∈ PJset O ϖ r c
    · obtain ⟨p₀, hp₀, k₀, hk₀, rfl⟩ := hg
      rw [← mul_assoc, fvec_eq hgrp hlam hfix (bDA_mul hp hp₀) hk₀, fvec_eq hgrp hlam hfix hp₀ hk₀,
        chiP_mul nrm δ hp hp₀, lev_mul hp hp₀, map_mul, map_smul, smul_smul]
      rw [mul_assoc]
      rfl
    · rw [fvec_out hgrp hg, fvec_out hgrp (fun h => hg ((mul_mem_PJ_iff hgrp hp).1 h)), map_zero, smul_zero]
  · by_cases hg : g ∈ PJset O ϖ r c
    · obtain ⟨p₀, hp₀, k₀, hk₀, rfl⟩ := hg
      rw [mul_assoc, fvec_eq hgrp hlam hfix hp₀ (hgrp _ _ hk₀ hk).1, fvec_eq hgrp hlam hfix hp₀ hk₀, smul_smul,
        hlam _ _ hk₀ hk]
      congr 1
      ring
    · rw [fvec_out hgrp hg, fvec_out hgrp (fun h => hg ((mul_mem_PJ_iff' hgrp hk).1 h)), smul_zero]

end Mem

section Adic

theorem det_mem_of_int {F : Type} [Field F] {O : Subring F} {n : ℕ} {M : Matrix (Fin n) (Fin n) F}
    (h : ∀ a b, M a b ∈ O) : M.det ∈ O := by
  let M' : Matrix (Fin n) (Fin n) O := fun i j => ⟨M i j, h i j⟩
  have e : M = O.subtype.mapMatrix M' := rfl
  rw [e, ← RingHom.map_det]
  exact (M'.det).2

theorem bAA_one {F : Type} [Field F] {r c : ℕ} :
    bAA ((1 : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
  ext i j
  simp [bAA, Matrix.one_apply, Fin.ext_iff]

theorem bDD_one {F : Type} [Field F] {r c : ℕ} :
    bDD ((1 : GL (Fin (r + c)) F) : Matrix (Fin (r + c)) (Fin (r + c)) F) = 1 := by
  ext i j
  simp [bDD, Matrix.one_apply, Fin.ext_iff]

theorem lev_inv {F : Type} [Field F] {r c : ℕ} {q : GL (Fin (r + c)) F}
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) :
    (levA q)⁻¹ = levA q⁻¹ ∧ (levD q)⁻¹ = levD q⁻¹ := by
  have h := lev_mul hq (bDA_inv hq)
  have hA : levA (q * q⁻¹) = 1 := Units.ext (by rw [mul_inv_cancel, levA_val bDA_one, bAA_one]; rfl)
  have hD : levD (q * q⁻¹) = 1 := Units.ext (by rw [mul_inv_cancel, levD_val bDA_one, bDD_one]; rfl)
  rw [hA, hD] at h
  exact ⟨(eq_inv_of_mul_eq_one_right (congrArg Prod.fst h).symm).symm,
    (eq_inv_of_mul_eq_one_right (congrArg Prod.snd h).symm).symm⟩

theorem lev_mem_GLint {F : Type} [Field F] {O : Subring F} {r c : ℕ} {q : GL (Fin (r + c)) F}
    (hq : bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) F) = 0) (hK : q ∈ GLint O (r + c)) :
    levA q ∈ GLint O r ∧ levD q ∈ GLint O c := by
  have hK' : q⁻¹ ∈ GLint O (r + c) := inv_mem hK
  obtain ⟨e1, e2⟩ := lev_inv hq
  refine ⟨⟨fun a b => ?_, fun a b => ?_⟩, ⟨fun a b => ?_, fun a b => ?_⟩⟩
  · rw [levA_val hq]; exact hK.1 _ _
  · rw [e1, levA_val (bDA_inv hq)]; exact hK'.1 _ _
  · rw [levD_val hq]; exact hK.1 _ _
  · rw [e2, levD_val (bDA_inv hq)]; exact hK'.1 _ _

variable {L : Type} [Field L] [NumberField L]

theorem nrm_det_GLint {P : HeightOneSpectrum (𝓞 L)} {nrm : AbsoluteValue (P.adicCompletion L) ℝ} (hn : IsNrm P nrm)
    {n : ℕ} {m : GL (Fin n) (P.adicCompletion L)} (hm : m ∈ GLint (OP P) n) :
    nrm (m : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det = 1 := by
  have h1 : Valued.v (m : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det ≤ 1 := det_mem_of_int hm.1
  have h2 : Valued.v ((m⁻¹ : GL (Fin n) (P.adicCompletion L)) : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det ≤ 1 :=
    det_mem_of_int hm.2
  have e : ((m⁻¹ : GL (Fin n) (P.adicCompletion L)) : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det =
      ((m : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rw [e, map_inv₀] at h2
  have h0 : Valued.v (m : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det ≠ 0 := by
    simp [m.det_ne_zero]
  have hv : Valued.v (m : Matrix (Fin n) (Fin n) (P.adicCompletion L)).det = 1 :=
    le_antisymm h1 (by
      by_contra hc
      push_neg at hc
      have := one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 h0, hc⟩
      exact absurd h2 (not_le.2 this))
  exact (hn (Units.mk0 _ m.det_ne_zero)).1 hv

end Adic

section Final

variable {L : Type} [Field L] [NumberField L]

theorem norm_unitCharExtendedByZero_eq_one {P : HeightOneSpectrum (𝓞 L)} {δ : (P.adicCompletion L)ˣ →* ℂˣ} (hδ : IsDel P δ)
    {x : P.adicCompletion L} (hx : x ≠ 0) : ‖chi0 δ x‖ = 1 := by
  rw [chi0, dif_neg hx]
  exact hδ.unitary _

theorem piP_mem (P : HeightOneSpectrum (𝓞 L)) : (piP P : P.adicCompletion L) ∈ OP P := by
  show Valued.v (piP P : P.adicCompletion L) ≤ 1
  have h : Valued.v (piP P : P.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec P
  rw [h, ← WithZero.exp_zero]
  exact WithZero.exp_le_exp.2 (by norm_num)

theorem exists_typeVec (P : HeightOneSpectrum (𝓞 L)) (δ : (P.adicCompletion L)ˣ →* ℂˣ) (hδ : IsDel P δ)
    (nrm : AbsoluteValue (P.adicCompletion L) ℝ) (hn : IsNrm P nrm) (r c : ℕ)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : GL (Fin r) (P.adicCompletion L) × GL (Fin c) (P.adicCompletion L) →* (V ≃ₗᵢ[ℂ] V)) (v₀ : V) (hv : ‖v₀‖ = 1)
    (hfix₀ : ∀ k₁ ∈ GLint (OP P) r, ∀ k₂ ∈ GLint (OP P) c, ρ (k₁, k₂) v₀ = v₀) :
    ∃ f ∈ typeSp (OP P) (piP P : P.adicCompletion L) nrm δ r c ρ, ∃ U : Set (GL (Fin (r + c)) (P.adicCompletion L)),
      IsOpen U ∧ parJ (OP P) (piP P : P.adicCompletion L) r c ⊆ U ∧
      ∀ k ∈ GLint (OP P) (r + c), ‖f k‖ = U.indicator 1 k := by
  have hgrp := _root_.GlobalTheory.ParGroup.parJ_mul_inv (P.adicCompletion L) (OP P) (piP P : P.adicCompletion L) (piP_mem P) r c
  have hlam := _root_.GlobalTheory.Mem.LamMul.lamJ_mul L P δ hδ r c
  have hfix : ∀ q : GL (Fin (r + c)) (P.adicCompletion L), q ∈ parJ (OP P) (piP P : P.adicCompletion L) r c →
      bDA (q : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) = 0 →
      ρ (levA q, levD q) v₀ = v₀ ∧ chiP nrm δ q = lamJ δ q := by
    intro q hq h0
    obtain ⟨h1, h2⟩ := lev_mem_GLint h0 hq.1
    refine ⟨hfix₀ _ h1 _ h2, ?_⟩
    rw [chiP, lamJ, ← levA_val h0, ← levD_val h0, nrm_det_GLint hn h1, nrm_det_GLint hn h2]
    simp
  have hlam1 : lamJ δ (1 : GL (Fin (r + c)) (P.adicCompletion L)) = 1 := by
    rw [lamJ, bDD_one, det_one, chi0, dif_neg one_ne_zero]
    have : Units.mk0 (1 : P.adicCompletion L) one_ne_zero = 1 := Units.ext rfl
    rw [this, map_one, Units.val_one]
  refine ⟨fvec (OP P) (piP P : P.adicCompletion L) nrm δ ρ v₀, fvec_mem hgrp hlam hfix,
    PJset (OP P) (piP P : P.adicCompletion L) r c, ?_, fun k hk => ⟨1, bDA_one, k, hk, (one_mul k).symm⟩,
    fun k hk => ?_⟩
  · have ho := (_root_.GlobalTheory.ParahoricTopo.isOpen_isCompact_parJ L P r c).1
    have e : PJset (OP P) (piP P : P.adicCompletion L) r c = ⋃ p : {p : GL (Fin (r + c)) (P.adicCompletion L) //
        bDA (p : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) = 0},
        (fun g => p.1 * g) '' parJ (OP P) (piP P : P.adicCompletion L) r c := by
      ext g
      simp only [Set.mem_iUnion, Set.mem_image]
      constructor
      · rintro ⟨p, hp, k, hk, rfl⟩; exact ⟨⟨p, hp⟩, k, hk, rfl⟩
      · rintro ⟨⟨p, hp⟩, k, hk, rfl⟩; exact ⟨p, hp, k, hk, rfl⟩
    rw [e]
    exact isOpen_iUnion fun p => (Homeomorph.mulLeft p.1).isOpenMap _ ho
  · by_cases hg : k ∈ PJset (OP P) (piP P : P.adicCompletion L) r c
    · rw [Set.indicator_of_mem hg, Pi.one_apply]
      obtain ⟨p, hp, k₀, hk₀, rfl⟩ := hg
      rw [fvec_eq hgrp hlam hfix hp hk₀, norm_smul, LinearIsometryEquiv.norm_map, hv, mul_one, norm_mul]
      have hpK : p ∈ GLint (OP P) (r + c) := by
        have : p = p * k₀ * k₀⁻¹ := by simp
        rw [this]; exact mul_mem hk (inv_mem hk₀.1)
      obtain ⟨h1, h2⟩ := lev_mem_GLint hp hpK
      have hc : ‖chiP nrm δ p‖ = 1 := by
        rw [chiP, ← levA_val hp, ← levD_val hp, nrm_det_GLint hn h1, nrm_det_GLint hn h2]
        simp only [Real.one_rpow, mul_one, Complex.ofReal_one, one_mul]
        exact norm_unitCharExtendedByZero_eq_one hδ (levD p).det_ne_zero
      have hl : ‖lamJ δ k₀‖ = 1 := by
        have e := hlam _ _ hk₀ (hgrp _ _ hk₀ hk₀).2
        rw [mul_inv_cancel, hlam1] at e
        have hne : (bDD (k₀ : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).det ≠ 0 := by
          intro h0
          simp only [lamJ] at e
          rw [h0] at e
          simp [chi0] at e
        exact norm_unitCharExtendedByZero_eq_one hδ hne
      rw [hc, hl, mul_one]
    · rw [Set.indicator_of_notMem hg, fvec_out hgrp hg, norm_zero]

end Final

section Haar

variable {L : Type} [Field L] [NumberField L]

theorem one_mem_parJ (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ) :
    (1 : GL (Fin (r + c)) (P.adicCompletion L)) ∈ parJ (OP P) (piP P : P.adicCompletion L) r c := by
  refine ⟨one_mem _, fun i j => ⟨0, (OP P).zero_mem, ?_⟩⟩
  simp [bDA, Matrix.one_apply, Fin.ext_iff]
  omega
theorem KO_eq_GLint (P : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    letI := GlobalTheory.LocalData.complRel P
    GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin n) = GLint (OP P) n := by
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (P.adicCompletion L))
    (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ)))
  ext g
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  simp only [he.le_one_iff_le_one, Valuation.mem_integer_iff]
  exact Iff.rfl

theorem isCompact_GLint (P : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    IsCompact (GLint (OP P) n : Set (GL (Fin n) (P.adicCompletion L))) := by
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  rw [← KO_eq_GLint]
  exact GlobalTheory.SplitFlip.isCompact_KO

theorem isOpen_GLint (P : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    IsOpen (GLint (OP P) n : Set (GL (Fin n) (P.adicCompletion L))) := by
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  rw [← KO_eq_GLint]
  exact GlobalTheory.SplitFlip.isOpen_KO

theorem exists_haar_parJ (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ) :
    letI : MeasurableSpace (P.adicCompletion L) := borel _
    ∃ μ : Measure (GL (Fin (r + c)) (P.adicCompletion L)), μ.IsMulLeftInvariant ∧
      μ (parJ (OP P) (piP P : P.adicCompletion L) r c) = 1 ∧ μ (GLint (OP P) (r + c)) < ⊤ := by
  letI : MeasurableSpace (P.adicCompletion L) := borel _
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  obtain ⟨ho, hc⟩ := _root_.GlobalTheory.ParahoricTopo.isOpen_isCompact_parJ L P r c
  let K₀ : TopologicalSpace.PositiveCompacts (GL (Fin (r + c)) (P.adicCompletion L)) :=
    ⟨⟨_, hc⟩, by
      rw [ho.interior_eq]
      exact ⟨1, one_mem_parJ P r c⟩⟩
  refine ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self, ?_⟩
  exact (isCompact_GLint P _).measure_lt_top

end Haar

theorem exists_typeDim_step : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)), Deg1 P → ∀ (δ : (P.adicCompletion L)ˣ →* ℂˣ) (ν : ℕ → (P.adicCompletion L)ˣ →* ℂˣ), IsDel P δ → (∀ i, IsNu P (ν i)) → ∀ r t j : ℕ, 1 ≤ t → (∃ n, TypeDimAt P δ ν r t j n) ∧ ∃ z, StepAt P δ ν r t j z := by
  intro L _ _ P _ δ ν hδ hν r t j ht
  obtain ⟨nrm, hn⟩ := GlobalTheory.Mem.NrmCompl.exists_isNrm L P
  obtain ⟨V, i1, i2, ρ, hρ⟩ := GlobalTheory.SphCyclic.exists_isUnrM L P nrm hn ν hν r t j ht
  refine ⟨⟨_, nrm, hn, V, i1, i2, ρ, hρ, rfl⟩, ?_⟩
  letI : MeasurableSpace (P.adicCompletion L) := borel _
  obtain ⟨v₀, hv, hfix, -⟩ := hρ.sph
  obtain ⟨f, hf, U, hU, hJU, hfn⟩ := exists_typeVec P δ hδ nrm hn r (j * t) ρ v₀ hv hfix
  obtain ⟨μ, hμ, hμ1, hμK⟩ := exists_haar_parJ P r (j * t)
  obtain ⟨dx, hdx, -, hdx1⟩ := GlobalTheory.HaarMat.exists_haar_intMat L P (r + (j + 1) * t) (r + j * t)
  set K : Set (GL (Fin (r + j * t)) (P.adicCompletion L)) := ((GLint (OP P) (r + j * t) : Subgroup _) : Set (GL (Fin (r + j * t)) (P.adicCompletion L)))
  have hUm : MeasurableSet U := hU.measurableSet
  have hsub : parJ (OP P) (piP P : P.adicCompletion L) r (j * t) ⊆ K ∩ U := fun x hx => ⟨hx.1, hJU hx⟩
  have hc1 : 1 ≤ μ (K ∩ U) := hμ1 ▸ measure_mono hsub
  have hcT : μ (K ∩ U) < ⊤ := (measure_mono Set.inter_subset_left).trans_lt hμK
  set c : ℝ := μ.real (K ∩ U)
  have hcpos : 0 < c := ENNReal.toReal_pos (by positivity) hcT.ne
  have key : ∀ (g : GL (Fin (r + j * t)) (P.adicCompletion L) → V) (a : ℝ),
      (∀ k ∈ K, ‖g k‖ = a * U.indicator 1 k) → mcoef (OP P) μ g 1 = ((a ^ 2 * c : ℝ) : ℂ) := by
    intro g a hg
    unfold mcoef
    have e : ∀ k ∈ K, inner ℂ (g k) (g (k * 1)) =
        ((U.indicator (fun _ => a ^ 2) k : ℝ) : ℂ) := by
      intro k hk
      rw [mul_one, inner_self_eq_norm_sq_to_K, hg k hk]
      by_cases h : k ∈ U <;> simp [h]
    rw [setIntegral_congr_fun (isOpen_GLint P _).measurableSet e, integral_complex_ofReal,
      setIntegral_indicator hUm, setIntegral_const, smul_eq_mul, mul_comm]
  refine ⟨_, nrm, hn, V, i1, i2, ρ, hρ, ((c ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • f, Submodule.smul_mem _ _ hf, μ, dx, hμ, hμ1, ?_,
    hdx, hdx1, rfl⟩
  rw [key _ (c ^ (-(1 / 2 : ℝ))) (fun k hk => ?_)]
  · have h2 : (c ^ (-(1 / 2 : ℝ))) ^ 2 = c⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hcpos.le]
      norm_num
      exact Real.rpow_neg_one c
    rw [h2, inv_mul_cancel₀ hcpos.ne', Complex.ofReal_one]
  · rw [Pi.smul_apply, norm_smul, hfn k hk, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hcpos.le _)]

end GlobalTheory.TypeStep
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOne =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlace =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlace", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPair\nimport Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.RamificationInertia.Basic\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Formalism.DoubleCosetMeasures.Statement\nimport Formalism.LocalToGlobal.Divisibility.QLocTied\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section
namespace GlobalTheory.Mem.HD.RamBoth

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
  simpa using h

theorem exists_intCast_cong {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (hp : (Ideal.absNorm w.asIdeal).Prime) (z : w.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ k : ℤ, Valued.v (algebraMap E (w.adicCompletion E) (k : E) - z) ≤ WithZero.exp (-1 : ℤ) := by
  obtain ⟨b, hb⟩ := GlobalTheory.CMVal.Euler.SplitPair.exists_int_cong w z hz
  have hc : Nat.card (𝓞 E ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Fact (Nat.card (𝓞 E ⧸ w.asIdeal)).Prime := ⟨hc ▸ hp⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  have htop : AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) = ⊤ := by
    rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card (AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal)) with h | h
    · exfalso
      have : (1 : 𝓞 E ⧸ w.asIdeal) ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := AddSubgroup.mem_zmultiples 1
      rw [h, AddSubgroup.mem_bot] at this
      exact one_ne_zero this
    · exact h
  obtain ⟨k, hk⟩ : Ideal.Quotient.mk w.asIdeal b ∈ AddSubgroup.zmultiples (1 : 𝓞 E ⧸ w.asIdeal) := htop ▸ AddSubgroup.mem_top _
  have hk' : ((k : 𝓞 E ⧸ w.asIdeal)) = Ideal.Quotient.mk w.asIdeal b := by simpa using hk
  have hmem : b - (k : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hk', map_intCast, sub_self]
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((b : E) - (k : E))) ≤ WithZero.exp (-1 : ℤ) := by
    have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [hval]
    refine le_exp_neg_one_of_lt_one ?_
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (b - (k : 𝓞 E))).2 hmem
    simpa using this
  have hb' : Valued.v (algebraMap E (w.adicCompletion E) (b : E) - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := hb
  refine ⟨k, ?_⟩
  have := Valuation.map_sub_le _ (hb'.trans (by simp)) h1
  rw [map_sub (algebraMap E (w.adicCompletion E)), sub_sub_sub_cancel_left] at this
  exact this

theorem mem_aboveF_iff (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {R : HeightOneSpectrum (𝓞 D.host.E)} :
    R ∈ aboveF (L := D.host.E) D.host.F v ↔ R.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl


open Classical in
theorem aboveF_eq_pair (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w P : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ aboveF (L := D.host.E) D.host.F v) (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (hne : w ≠ P) :
    aboveF (L := D.host.E) D.host.F v = {w, P} := by
  haveI := v.isMaximal
  haveI : NoZeroSMulDivisors (𝓞 D.host.F) (𝓞 D.host.E) := ⟨fun {c x} e => by
    rw [Algebra.smul_def, mul_eq_zero,
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))] at e
    exact e⟩
  have h1 := Ideal.card_primesOverFinset_le_finrank (𝓞 D.host.E) D.host.F D.host.E v.ne_bot
  rw [D.sp.cm.deg2] at h1
  have h2 : (aboveF (L := D.host.E) D.host.F v).card ≤ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 D.host.E)).card := by
    refine Finset.card_le_card_of_injOn HeightOneSpectrum.asIdeal (fun R hR => ?_)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
    rw [Finset.mem_coe, mem_aboveF_iff] at hR
    rw [IsDedekindDomain.coe_primesOverFinset v.ne_bot]
    exact ⟨R.isPrime, ⟨hR ▸ rfl⟩⟩
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro R hR
    rw [Finset.mem_insert, Finset.mem_singleton] at hR
    rcases hR with rfl | rfl <;> assumption
  · rw [Finset.card_pair hne]; omega

theorem unrAt_of_pair {E : Type} [Field E] [NumberField E] {F : Type} [Field F] [NumberField F] [Algebra F E]
    [DecidableEq (HeightOneSpectrum (𝓞 E))] (χ : HChar E) {v : HeightOneSpectrum (𝓞 F)} {w P : HeightOneSpectrum (𝓞 E)}
    (hw : w.under (𝓞 F) = v) (hP : P.under (𝓞 F) = v) (hne : w ≠ P) (hS : aboveF (L := E) F v = {w, P})
    (hp : (Ideal.absNorm w.asIdeal).Prime) (hF : χ.TrivOn F) (ht : χ.TameAt w) (hun : χ.UnrAt P) : χ.UnrAt w := by
  intro u hu
  have hu1 : Valued.v (u : w.adicCompletion E) = 1 := hu
  obtain ⟨k, hk⟩ := exists_intCast_cong w hp u hu1.le
  have hval : ∀ (R : HeightOneSpectrum (𝓞 E)), Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = 1 ↔
      (k : 𝓞 E) ∉ R.asIdeal := fun R => by
    have h1 : Valued.v (algebraMap E (R.adicCompletion E) (k : E)) = R.valuation E (k : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' R (k : E)
    have h2 : R.valuation E (k : E) = R.intValuation (k : 𝓞 E) := by
      rw [← map_intCast (algebraMap (𝓞 E) E) k]
      exact HeightOneSpectrum.valuation_of_algebraMap (K := E) R (k : 𝓞 E)
    rw [h1, h2, HeightOneSpectrum.intValuation_eq_one_iff]
  have hmem : ∀ (R : HeightOneSpectrum (𝓞 E)), R.under (𝓞 F) = v → ((k : 𝓞 E) ∈ R.asIdeal ↔ (k : 𝓞 F) ∈ v.asIdeal) :=
    fun R hR => by
      rw [← hR, ← map_intCast (algebraMap (𝓞 F) (𝓞 E)) k]
      exact Iff.rfl
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have h5 : Valued.v (algebraMap E (w.adicCompletion E) (k : E)) = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ hk.trans_lt hlt), hu1]
  have hkw := (hval w).1 h5
  have hkP : (k : 𝓞 E) ∉ P.asIdeal := fun h => hkw ((hmem w hw).2 ((hmem P hP).1 h))
  have hk0 : (k : F) ≠ 0 := by
    intro h
    have : k = 0 := by exact_mod_cast h
    exact hkw (by simp [this])
  have hco : ∀ R : HeightOneSpectrum (𝓞 E), ((atFin R (upF F (Units.mk0 (k : F) hk0)) : (R.adicCompletion E)ˣ) :
      R.adicCompletion E) = algebraMap E (R.adicCompletion E) (k : E) := fun R => by
    rw [← map_intCast (algebraMap F E) k]
    rfl
  have h7 := hF.1 v (Units.mk0 (k : F) hk0)
  unfold HChar.resFin at h7
  rw [MonoidHom.finsetProd_apply, hS, Finset.prod_pair hne] at h7
  have h6 : χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 := hun _ (by
    unfold IsUnitAt
    rw [hco, (hval P).2 hkP])
  change χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0))) * χ.loc P (atFin P (upF F (Units.mk0 (k : F) hk0))) = 1 at h7
  rw [h6, mul_one] at h7
  have h8 : χ.loc w (atFin w (upF F (Units.mk0 (k : F) hk0)) / u) = 1 := by
    refine ht _ ?_ ?_
    · unfold IsUnitAt
      rw [Units.val_div_eq_div_val, map_div₀, hco, h5, hu1, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, hco]
      exact hk
  rw [map_div, div_eq_one, h7] at h8
  exact h8.symm

theorem ram_both : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp →
    ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)),
    w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v →
    ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := by
  classical
  intro D C nch Tp hT μ v w P hw hP hr hun
  by_cases hne : w = P
  · exact hr (hne ▸ hun)
  · exact hr (unrAt_of_pair _ ((mem_aboveF_iff D).1 hw) ((mem_aboveF_iff D).1 hP) hne
      (by convert aboveF_eq_pair D hw hP hne) (hT.ram μ w hr).2.1 (Tp.xi_triv μ) (Tp.xi_tame μ w) hun)

end GlobalTheory.Mem.HD.RamBoth

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlace =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty", "h": "module\n\npublic import Formalism.LocalToGlobal.Divisibility.QLocTied\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins\npublic import Mathlib.Tactic.Linter.HaveILetI\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypeDimensionAndLocalIntegralsDegreeOne\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SingleBlockDoublingIntegralValue\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleCharRamifiedAtAllPrimesOverPlace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

noncomputable section

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

theorem mem_aboveF_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)} :
    P ∈ aboveF (L := D.host.E) D.host.F v ↔ P.under (𝓞 D.host.F) = v := by
  rw [aboveF, Set.Finite.mem_toFinset]; rfl

theorem absNorm_eq_of_mem {v : HeightOneSpectrum (𝓞 D.host.F)} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : P ∈ aboveF (L := D.host.E) D.host.F v) (h : (Ideal.absNorm P.asIdeal).Prime) :
    Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
  rw [mem_aboveF_iff] at hP
  subst hP
  have hd : Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal ∣ Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact AddSubgroup.card_dvd_of_injective
      (Ideal.quotientMap P.asIdeal (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) le_rfl).toAddMonoidHom
      Ideal.quotientMap_injective
  exact ((Nat.dvd_prime h).1 hd).resolve_left fun h1 =>
    (P.under (𝓞 D.host.F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h1)

theorem eq_exp_of_le {x : WithZero (Multiplicative ℤ)} {m : ℤ} (h : x ≤ WithZero.exp m)
    (h' : ¬ x ≤ WithZero.exp (m - 1)) : x = WithZero.exp m := by
  refine le_antisymm h (not_lt.1 fun h1 => h' ?_)
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, sub_add_cancel]
  exact h1

theorem degreeOne_of_prime_absNorm_not_mem_sq {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
    (h1 : (Ideal.absNorm P.asIdeal).Prime) (h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∉ P.asIdeal ^ 2) : Deg1 P := by
  refine ⟨h1, ?_⟩
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ∈ P.asIdeal := Ideal.absNorm_mem _
  have e : ((qP P : ℕ) : P.adicCompletion L) =
      algebraMap L (P.adicCompletion L) (algebraMap (𝓞 L) L ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L)) := by
    simp [qP]
  have hv : ∀ y : L, Valued.v (algebraMap L (P.adicCompletion L) y) = P.valuation L y := fun y =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P y
  rw [e, hv, HeightOneSpectrum.valuation_of_algebraMap]
  have a1 := (P.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hmem)
  have a2 : ¬ P.intValuation ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem _ 2).1 h)
  refine eq_exp_of_le (by simpa using a1) fun h => a2 ?_
  convert h using 2
  norm_num

theorem ramTransfer : ∀ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch), TupPins Tp → ∀ (μ : D.what₂.Tup) (v : HeightOneSpectrum (𝓞 D.host.F)) (w P : HeightOneSpectrum (𝓞 D.host.E)), w ∈ aboveF (L := D.host.E) D.host.F v → P ∈ aboveF (L := D.host.E) D.host.F v → ¬ (Tp.xi μ).UnrAt w → ¬ (Tp.xi μ).UnrAt P := _root_.GlobalTheory.Mem.HD.RamBoth.ram_both

theorem finite_inQ (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {v : HeightOneSpectrum (𝓞 D.host.F) | Tp.InQ' μ v}.Finite := by
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).image fun w => w.under (𝓞 D.host.F)).subset ?_
  rintro v ⟨w, hw, hr⟩
  exact ⟨w, hr, mem_aboveF_iff.1 hw⟩

theorem prime_eq_of_overP {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h1 : OverP D.host p w) (h2 : OverP D.host q w) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have h : ((a * p + b * q : ℤ) : 𝓞 D.host.E) ∈ w.asIdeal := by
    push_cast
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ (by exact_mod_cast h1))
      (w.asIdeal.mul_mem_left _ (by exact_mod_cast h2))
  rw [hab, Int.cast_one] at h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem finite_qp (Tp : TupTied D C nch) (μ : D.what₂.Tup) :
    {p : ℕ | p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w}.Finite := by
  have hs : ∀ w : HeightOneSpectrum (𝓞 D.host.E), Set.Subsingleton {p : ℕ | p.Prime ∧ OverP D.host p w} :=
    fun w p hp q hq => prime_eq_of_overP hp.1 hq.1 hp.2 hq.2
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified (Tp.xi μ)).biUnion fun w _ => (hs w).finite).subset ?_
  rintro p ⟨hp, w, hw, hr⟩
  exact Set.mem_biUnion hr ⟨hp, hw⟩

def qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) : Finset ℕ := (finite_qp Tp μ).toFinset

theorem mem_qpSet (Tp : TupTied D C nch) (μ : D.what₂.Tup) (p : ℕ) :
    p ∈ qpSet Tp μ ↔ p.Prime ∧ ∃ w, OverP D.host p w ∧ ¬ (Tp.xi μ).UnrAt w := by
  rw [qpSet, Set.Finite.mem_toFinset]; rfl

theorem ramifiedRationalPrimesOfTuple_baseTuple_eq_empty (Tp : TupTied D C nch) : qpSet Tp D.what₂.mu0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨-, w, -, hr⟩ := (mem_qpSet Tp _ p).1 hp
  exact hr fun x _ => by rw [Tp.trueColumnChoices_heckeChar_reference_eq_one]; rfl

theorem qpSet_muAt (Tp : TupTied D C nch) (hp : TupPins Tp) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w ∉ qpSet Tp (D.what₂.muAt w) := fun h => by
  obtain ⟨-, w', hw', hr⟩ := (mem_qpSet Tp _ _).1 h
  exact hr (hp.atl w w' hw')

theorem qpSet_g (Tp : TupTied D C nch) (hp : TupPins Tp) (μ : D.what₂.Tup) (i : Fin 2) :
    D.host.g i ∉ qpSet Tp μ := fun h => by
  obtain ⟨-, w, hw, hr⟩ := (mem_qpSet Tp _ _).1 h
  exact (hp.ram μ w hr).2.2.2 i hw

theorem one_lt_absNorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) :
    1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)


include hp hPv in
theorem ram_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ¬ (Tp.xi μ).UnrAt (Pv v.1) := by
  obtain ⟨w, hw, hr⟩ := v.2
  exact ramTransfer D C nch Tp hp μ v.1 w (Pv v.1) hw (hPv v.1) hr

include hp hPv in
theorem chosenPrimeAbove_ramifiedPlace_degreeOne (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : Deg1 (Pv v.1) :=
  degreeOne_of_prime_absNorm_not_mem_sq _ (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1 (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.1

include hp hPv in
theorem offg_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    ∀ k, ¬ OverP D.host (D.host.g k) (Pv v.1) :=
  (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.2.2

include hp hPv in
theorem absNorm_Pv (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) :
    Ideal.absNorm v.1.asIdeal = qP (Pv v.1) :=
  absNorm_eq_of_mem (hPv v.1) (hp.ram μ _ (ram_Pv Tp hp Pv hPv μ v)).2.1

theorem one_le_letterBlockLength : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega


include hp hPv in
theorem stepEx (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) (j : ℕ) :
    (∃ n, TypeDimAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j n) ∧
      ∃ z, StepAt (Pv v.1) (delQ Tp μ (Pv v.1)) (nuP C (Pv v.1)) D.R.r D.R.t j z :=
  _root_.GlobalTheory.TypeStep.exists_typeDim_step D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _ (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v))
    (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v)) D.R.r D.R.t j one_le_letterBlockLength

def zq (μ : D.what₂.Tup) (v : {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}) : ℕ → ℂ
  | 0 => 0
  | j + 1 => (stepEx Tp hp Pv hPv μ v j).2.choose

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}
variable (Tp : TupTied D C nch) (hp : TupPins Tp) (Pv : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
  (hPv : ∀ v, Pv v ∈ aboveF (L := D.host.E) D.host.F v)

def reQ (Z₀ : DivX D) : DivX D :=
  { Z₀ with
    Qp := qpSet Tp
    degreeZero_partial_set_empty := ramifiedRationalPrimesOfTuple_baseTuple_eq_empty Tp
    Qp_muAt := qpSet_muAt Tp hp
    Qp_g := fun μ _ i => qpSet_g Tp hp μ i
    QPl := fun μ => {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v}
    finQ := fun μ => by
      haveI : Finite {v : HeightOneSpectrum (𝓞 D.host.F) // Tp.InQ' μ v} := (finite_inQ Tp μ).to_subtype
      exact Fintype.ofFinite _
    qv := fun _ v => Ideal.absNorm v.1.asIdeal
    qv_gt := fun _ v => one_lt_absNorm v.1
    qv_char := fun μ _ v => by
      obtain ⟨w, hw, hr⟩ := v.2
      have hpr := (hp.ram μ w hr).2.1
      refine ⟨Ideal.absNorm v.1.asIdeal, (mem_qpSet Tp μ _).2 ⟨?_, w, ?_, hr⟩, ?_, rfl⟩
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
      · rw [absNorm_eq_of_mem hw hpr]; exact Ideal.absNorm_mem _
      · rw [absNorm_eq_of_mem hw hpr]; exact hpr
    nu := fun _ v i => ((nuP C (Pv v.1) i (piP (Pv v.1)) : ℂˣ) : ℂ)
    nu_ne := fun _ _ _ => Units.ne_zero _
    nu_abs := fun μ v i => (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) i).unitary _
    ZQ := zq Tp hp Pv hPv
    quotientLocalValueFirst := fun _ v => (zVal1 (qP (Pv v.1)) D.R.r D.R.t : ℂ)
    typeDim := fun μ v j => (stepEx Tp hp Pv hPv μ v j).1.choose }

def reducedDivisorCharacter (Z₀ : DivX D) : DivisorCharacterCompatibility D C nch Tp (reQ Tp hp Pv hPv Z₀) where
  Qp_iff := mem_qpSet Tp
  eQPl := fun _ => Equiv.refl _
  qv_eq := fun _ _ => rfl

theorem reLoc (Z₀ : DivX D) : QLocTiedC (reducedDivisorCharacter Tp hp Pv hPv Z₀) Pv := by
  refine ⟨fun μ v => hPv _, ?_⟩
  refine
    { qv_eq := fun μ v => absNorm_Pv Tp hp Pv hPv μ v
      deg1 := fun μ v => chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v
      ram := fun μ v => ram_Pv Tp hp Pv hPv μ v
      off_g := fun μ v => offg_Pv Tp hp Pv hPv μ v
      nu_eq := fun μ v i => ?_
      typeDim_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).1.choose_spec
      ZQ_eq := fun μ v j _ => (stepEx Tp hp Pv hPv μ v j).2.choose_spec
      quotientLocalValueFirst_eq := fun μ v j _ _ => _root_.GlobalTheory.Mem.SingleQ.stepAt_one D.host.E (Pv v.1) (chosenPrimeAbove_ramifiedPlace_degreeOne Tp hp Pv hPv μ v) _ _
        (isDel_delQ Tp μ (ram_Pv Tp hp Pv hPv μ v)) (isNu_nuP C (offg_Pv Tp hp Pv hPv μ v) j) D.R.r D.R.t one_le_letterBlockLength }
  show ((nuP C (Pv v.1) (i.1 + 1) (piP (Pv v.1)) : ℂˣ) : ℂ) = _
  rw [nuP_succ]
  rfl

end GlobalTheory.Mem.HD.ReQ

namespace GlobalTheory.Mem.HD.ReQ

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

end GlobalTheory.Mem.HD.ReQ
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RamifiedRationalPrimesOfTupleBaseTupleEqEmpty =====
