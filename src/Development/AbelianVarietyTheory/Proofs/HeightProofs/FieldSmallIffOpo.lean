module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevelsQDesc
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QuotientParamNonneg

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

namespace GlobalTheory.FinalJoin2

theorem FO_eq_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D = Q.c.F := by
  apply le_antisymm
  · rw [FO, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, rfl⟩
    have e := h (Q.eO.symm y)
    rw [RingEquiv.apply_symm_apply] at e
    have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
    rw [e']
    exact SetLike.coe_mem _
  · intro z hz
    haveI := Q.c.fin
    haveI : NumberField Q.c.F := NumberField.mk
    have hint : ∀ x : 𝓞 Q.c.F, ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) ∈ FO D := fun x => by
      have e : D.what₂.phiO (Q.eO x) = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) := h x
      rw [← e]
      exact phiO_mem_FO D _
    obtain ⟨x, y, -, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 Q.c.F) (⟨z, hz⟩ : Q.c.F)
    have : z = ((algebraMap (𝓞 Q.c.F) Q.c.F x : Q.c.F) : ℂ) / ((algebraMap (𝓞 Q.c.F) Q.c.F y : Q.c.F) : ℂ) := by
      have := congrArg (fun t : Q.c.F => (t : ℂ)) hxy
      simpa using this.symm
    rw [this]
    exact div_mem (hint x) (hint y)

theorem fieldSmall_iff_opo : ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D),
    FieldSmall D large₂ ↔ OPO large₂ (recB h.toLawsCore) := by
  intro D T h large₂
  have hF : FO D = T.Q.c.F := FO_eq_coeff T.Q h.toLawsCore.pins.2.2.1
  letI : NumberField (FO D) := NumberField.mk
  let e : FO D ≃+* (recB h.toLawsCore).KO := (IntermediateField.equivOfEq hF).toRingEquiv
  have h1 : Module.finrank ℚ (FO D) = Module.finrank ℚ (recB h.toLawsCore).KO :=
    (LinearEquiv.ofBijective e.toRingHom.toRatAlgHom.toLinearMap e.bijective).finrank_eq
  have h2 : NumberField.discr (FO D) = NumberField.discr (recB h.toLawsCore).KO :=
    NumberField.discr_eq_discr_of_ringEquiv _ e
  unfold FieldSmall OPO
  rw [← h1, ← h2]

end GlobalTheory.FinalJoin2
