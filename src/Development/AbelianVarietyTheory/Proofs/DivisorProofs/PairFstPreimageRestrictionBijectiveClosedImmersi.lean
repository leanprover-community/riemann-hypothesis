module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyBasisBijectiveStatement
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

private theorem exAff (Z : Scheme.{0}) {O : Z.Opens} {z : Z} (hz : z ∈ O) :
    ∃ V : Z.affineOpens, z ∈ V.1 ∧ V.1 ≤ O := by
  obtain ⟨V, hV, hzV, hVO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens hz
  exact ⟨⟨V, hV⟩, hzV, hVO⟩

theorem pair_pre_bijective : ∀ (R' : Type) [CommRing R'] (X Y Y' : Scheme.{0}) (ψ : Y ⟶ X) (χ : Y' ⟶ Y) [IsClosedImmersion χ] (q' : Y' ⟶ Sp R'), Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 ∧ (CohomZeroIsConstants (OAff q') → CohomZeroIsConstants (pairFst ψ ⋙ OPre χ q')) := by
  intro R' _ X Y Y' ψ χ _ q'
  have hG : Monotone (fun p : Pair ψ ↦ preU χ p.1.1) := fun _ _ h ↦ preU_mono χ (Pair.le_fst h)
  have hF : pairFst ψ ⋙ preAff χ = hG.functor.op := rfl
  have key := _root_.GlobalTheory.AbCoh.cohO_basis_bijective R' Y' q' (Pair ψ) (fun p ↦ preU χ p.1.1) hG ?cov ?dir
  · rw [hF]
    exact key
  case cov =>
    intro U x hx
    obtain ⟨t, ht, hte⟩ := χ.isClosedEmbedding.isInducing.isOpen_iff.1 U.1.2
    have hxt : χ x ∈ (⟨t, ht⟩ : Y.Opens) := by
      show χ x ∈ t
      rw [← Set.mem_preimage, hte]; exact hx
    obtain ⟨W, hW, -⟩ := exAff X (show ψ (χ x) ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨V, hV, hVle⟩ := exAff Y (show χ x ∈ (⟨t, ht⟩ : Y.Opens) ⊓ ψ ⁻¹ᵁ W.1 from ⟨hxt, hW⟩)
    refine ⟨⟨(V, W), fun y hy ↦ (hVle hy).2⟩, hV, ?_⟩
    intro y hy
    have : χ y ∈ t := (hVle hy).1
    rw [← Set.mem_preimage, hte] at this
    exact this
  case dir =>
    intro a b x ha hb
    have hya : ψ (χ x) ∈ a.1.2.1 := a.2 ha
    have hyb : ψ (χ x) ∈ b.1.2.1 := b.2 hb
    obtain ⟨W, hW, hWle⟩ := exAff X (show ψ (χ x) ∈ a.1.2.1 ⊓ b.1.2.1 from ⟨hya, hyb⟩)
    obtain ⟨V, hV, hVle⟩ := exAff Y
      (show χ x ∈ (a.1.1.1 ⊓ b.1.1.1) ⊓ ψ ⁻¹ᵁ W.1 from ⟨⟨ha, hb⟩, hW⟩)
    refine ⟨⟨(V, W), fun y hy ↦ (hVle hy).2⟩, ?_, ?_, hV⟩
    · exact ⟨fun y hy ↦ (hVle hy).1.1, fun y hy ↦ (hWle hy).1⟩
    · exact ⟨fun y hy ↦ (hVle hy).1.2, fun y hy ↦ (hWle hy).2⟩

end GlobalTheory.AbCoh
