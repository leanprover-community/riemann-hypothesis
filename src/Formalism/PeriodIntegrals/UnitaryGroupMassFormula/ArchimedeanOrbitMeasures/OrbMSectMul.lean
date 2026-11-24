module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.HaarUniqInf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem mem_H_iff (h : GI X) :
    h ∈ Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u') ↔
      h • ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) = ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) :=
  MulAction.mem_stabilizer_iff

theorem orbM_sect_mul (y : TupI X) (hy : ∃ g : GI X, orbM X u' g = y)
    (h : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) :
    orbM X u' (sect X u' y * (h : GI X)) = y := by
  have e1 := sect_spec X u' y hy
  unfold orbM at e1 ⊢
  rw [mul_smul, (mem_H_iff X u' h).1 h.2, e1]

theorem sect_smul (g : GI X) (y : TupI X) (hy : ∃ t : GI X, orbM X u' t = y) :
    ∃ h0 : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u'),
      sect X u' (g • y) = g * sect X u' y * (h0 : GI X) := by
  set Y := ratTup (F := X.B.I.F) (Ainf X.B.I.F) (tupH (frameOf X u')) with hY
  have e1 : sect X u' y • Y = y := sect_spec X u' y hy
  obtain ⟨t, ht⟩ := hy
  have e2 : sect X u' (g • y) • Y = g • y :=
    sect_spec X u' _ ⟨g * t, by rw [← ht]; exact mul_smul g t Y⟩
  set a := sect X u' y with ha
  set b := sect X u' (g • y) with hb
  refine ⟨⟨(g * a)⁻¹ * b, ?_⟩, ?_⟩
  · rw [mem_H_iff, mul_smul, e2]
    rw [← e1, show g • a • Y = (g * a) • Y from (mul_smul g a Y).symm, inv_smul_smul]
  · simp only [mul_inv_cancel_left]

theorem muH_preimage (μ : Measure (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')))
    [μ.IsMulLeftInvariant] (hne : μ ≠ 0)
    (h0 : Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u'))
    (S : Set (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u'))) (hS : MeasurableSet S) :
    μ ((fun h => h0 * h) ⁻¹' S) = μ S := by
  have hm : μ.map (fun h => h0 * h) = μ := map_mul_left_eq_self μ h0
  haveI : IsModuleTopology (Ainf X.B.I.F) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) :=
    IsModuleTopology.isTopologicalRing (Ainf X.B.I.F) _
  haveI : IsTopologicalGroup (GI X) := by
    have h {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
        (S : Subgroup G) : IsTopologicalGroup S := inferInstance
    exact h (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
  haveI : BorelSpace (GI X) := ⟨rfl⟩
  haveI : BorelSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u')) := inferInstance
  have ha : AEMeasurable (fun h => h0 * h) μ :=
    (measurable_const_mul h0).aemeasurable
  rw [← Measure.map_apply_of_aemeasurable ha hS, hm]

end PI.AprimeInfW
