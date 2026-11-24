module

public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigenInputs
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigen
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

theorem absNorm_extDifferent {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    letI _ : Algebra E L := ι.toAlgebra;
    Ideal.absNorm (extDifferent ι) = (discr E).natAbs ^ Module.finrank E L := by
  let _ : Algebra E L := ι.toAlgebra
  have h1 : RingOfIntegers.mapRingHom ι = algebraMap (𝓞 E) (𝓞 L) := rfl
  have h3 : Module.finrank (𝓞 E) (𝓞 L) = Module.finrank E L :=
    (IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L).symm
  rw [extDifferent, h1, Ideal.absNorm_algebraMap, absNorm_differentIdeal E (𝓞 E), h3]

theorem DifferentExtNorm.full : DifferentExtNorm.Statement := by
  intro E L _ _ _ _ ι
  refine ⟨extDifferent_ne_bot ι, ?_⟩
  let _ : Algebra E L := ι.toAlgebra
  have hN := absNorm_extDifferent ι
  have hd : (discr E) ≠ 0 := discr_ne_zero E
  have hE : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hdeg : Module.finrank ℚ L = Module.finrank ℚ E * Module.finrank E L :=
    (Module.finrank_mul_finrank ℚ E L).symm
  rw [hN, logRd, Nat.cast_pow, Real.log_pow, hdeg, Nat.cast_mul]
  have habs : ((discr E).natAbs : ℝ) = |(discr E : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  field_simp

end GroundTheory.Heights₂.Heights.NineStatements
