module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.exists_closedEmbedding_normOneAdelicGL_baseChange :
    N5 → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∃ j : G1 F n →* G1 E n, Topology.IsClosedEmbedding j ∧
        (∀ t : G1 F n, ((j t : G1 E n) : AdelicGLn.AdelicGL E n) = mapGL n (adeleMap F E) (t : AdelicGLn.AdelicGL F n)) ∧
        ∀ t : AdelicGLn.AdelicGL F n, mapGL n (adeleMap F E) t ∈ normOneGL (K := E) (n := n) → t ∈ normOneGL (K := F) (n := n) := by
  intro h5 F E _ _ _ _ _ _ σ hσ n hn
  obtain ⟨hemb, hdet, -⟩ := h5 F E σ hσ n hn
  have hpos : Module.finrank F E ≠ 0 := by
    haveI : FiniteDimensional F E := Module.Finite.right ℚ F E
    exact Module.finrank_pos.ne'
  have key : ∀ t : AdelicGLn.AdelicGL F n,
      mapGL n (adeleMap F E) t ∈ normOneGL (K := E) (n := n) ↔ t ∈ normOneGL (K := F) (n := n) := by
    intro t
    rw [mem_normOneGL_iff_detModule, mem_normOneGL_iff_detModule, Subtype.ext_iff, Subtype.ext_iff]
    rw [hdet t]
    exact pow_eq_one_iff_of_nonneg (detModule F n t).2.le hpos
  let j : normOneGL (K := F) (n := n) →* normOneGL (K := E) (n := n) :=
    MonoidHom.codRestrict ((mapGL n (adeleMap F E) : AdelicGLn.AdelicGL F n →* AdelicGLn.AdelicGL E n).comp
      (normOneGL (K := F) (n := n)).subtype) (normOneGL (K := E) (n := n)) (fun t => (key t.1).2 t.2)
  refine ⟨j, ?_, fun t => rfl, fun t ht => (key t).1 ht⟩
  have hF : Topology.IsClosedEmbedding (Subtype.val : normOneGL (K := F) (n := n) → AdelicGLn.AdelicGL F n) :=
    (isClosed_normOneGL (K := F) (n := n)).isClosedEmbedding_subtypeVal
  have hE : Topology.IsEmbedding (Subtype.val : normOneGL (K := E) (n := n) → AdelicGLn.AdelicGL E n) :=
    Topology.IsEmbedding.subtypeVal
  have hc : Topology.IsClosedEmbedding ((Subtype.val : normOneGL (K := E) (n := n) → AdelicGLn.AdelicGL E n) ∘ j) :=
    hemb.comp hF
  exact Topology.IsClosedEmbedding.of_comp hE hc
