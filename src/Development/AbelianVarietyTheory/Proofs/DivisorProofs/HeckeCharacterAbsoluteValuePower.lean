module

public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import GroundTheory.GlobalFields.WeilGroups.QuasiCharacter
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

namespace GlobalTheory.HeckeNormPow

def toQC {K : Type} [Field K] [NumberField K] (χ : HChar K) : GroundTheory.Global.QuasiCharacter K where
  toMonoidHom := QuotientGroup.lift _ χ.1 (by
    rintro _ ⟨a, rfl⟩
    exact χ.2.2 a)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 χ.2.1

theorem norm_val_eq_rpow : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), ∃ s : ℝ,
    ∀ w : HeightOneSpectrum (𝓞 K), ‖((χ.val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ s := by
  intro K _ _ χ
  obtain ⟨s, hs⟩ := GroundTheory.Global.QuasiCharacter.exists_norm_eq_rpow (toQC χ)
  refine ⟨-s, fun w => ?_⟩
  have h1 := hs
    (GroundTheory.Global.IdeleClassGroup.mk K (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w))))
  rw [GroundTheory.Global.IdeleClassGroup.ideleModule_mk,
    GroundTheory.Global.ideleModule_finiteEmbedding_of_uniformizer (unif_spec w)] at h1
  have h2 : ((χ.val w : ℂˣ) : ℂ) = (((toQC χ) (GroundTheory.Global.IdeleClassGroup.mk K
      (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w)))) : ℂˣ) : ℂ) := rfl
  rw [h2, h1, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]

end GlobalTheory.HeckeNormPow
