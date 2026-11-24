module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemMapImmersionStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem alg_of_isClosedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (i : W' ⟶ W), IsSeparated f → IsClosedImmersion i → Alg f I →
    Alg (i ≫ f) I := by
  intro R _ I W W' f i hf hi hA t ht hp
  obtain ⟨hs, hsp, hc⟩ := GlobalTheory.T.compatibleReductionSystem_map_immersion R I W W' f i hf inferInstance t ht hp
  obtain ⟨T, hT, hred⟩ := hA _ hs hsp
  refine ⟨T.comap i, ?_, fun e => ?_⟩
  · have h1 : (T.comap i).subschemeι ≫ i ≫ f =
        (T.comapIso i).hom ≫ pullback.snd i T.subschemeι ≫ T.subschemeι ≫ f := by
      rw [← T.comapIso_hom_fst_assoc i, pullback.condition_assoc]
    rw [h1]
    infer_instance
  · rw [← (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1 R W W' f i, ← Scheme.IdealSheafData.comap_sup, hred e]
    exact hc e

end GlobalTheory.FormalAlg
