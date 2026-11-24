module

public import Formalism.LocalRingCardinality.DataLevel
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemIffForallMemLocalizeRingOfIntegers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection

@[expose] public section

namespace GlobalTheory.OverCompare

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ u ∈ _root_.Formalism.BasicNotions.intV E v, u * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) = 1 := by
  have hc0 : (c : F) ≠ 0 := by
    intro h
    apply hc
    rw [show c = 0 from RingOfIntegers.coe_eq_zero_iff.mp h]
    exact v.asIdeal.zero_mem
  have hmem : algebraMap F (v.adicCompletion F) (c : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [_root_.GlobalTheory.LocalLattice.algebraMap_mem_adicCompletionIntegers_iff,
      _root_.GlobalTheory.LocalLattice.mem_localRing_iff]
    refine ⟨c, hc, ?_⟩
    rw [Algebra.smul_def, show algebraMap (𝓞 F) F c = (c : F) from rfl, mul_inv_cancel₀ hc0]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  refine ⟨1 ⊗ₜ[F] algebraMap F (v.adicCompletion F) (c : F)⁻¹, ?_, ?_⟩
  · unfold _root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt _root_.Formalism.UG.intOE
    exact Subring.subset_closure (Or.inr ⟨⟨_, hmem⟩, rfl⟩)
  · unfold _root_.Formalism.UG.inclE
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, ← Algebra.TensorProduct.algebraMap_apply,
      ← Algebra.TensorProduct.algebraMap_apply', ← map_mul, inv_mul_cancel₀ hc0, map_one]

end GlobalTheory.OverCompare
