module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGlueCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAFG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumATools
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumATop
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Top2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem latSide_at' (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hR : ClaimR M r n) : LatSide M r n :=
  latSide_at M r n hM hE hV hP (gramMM_holds M r n) (thFG_at M r hM) (thSpan_at M r hM) hR

theorem localCount_of_glue (M : Model F E) (r n : ℕ) (hM : M.OK) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hR : ClaimR M r n) (h0 : ModSide0 M r n M.split.isSome)
    (hU : ModSideU M r n M.split.isSome) : Formalism.MainNotions.ThinScalesBound.FamilyLocalModel M r n := by
  intro V _ _ H hn t₁ hg f₂ f₂' φ φ' hF hF' hI hs hs'
  have hT : LocalCountHypotheses H t₁ f₂ f₂' φ φ' := ⟨hg, hF, hF', hI, hs, hs'⟩
  have hL := latSide_at' M r n hM hE hV hP hR V H hn t₁ f₂ f₂' φ φ' hT
  dsimp only
  refine ⟨fun hz Z₁ Z₂ h₁ h₂ => ?_, fun hu Y₁ Y₂ be₁ be₂ al₁ al₂ hY hb => ?_⟩
  · rw [hL]
    exact h0 rfl V H hn t₁ f₂ f₂' φ φ' hT hz Z₁ Z₂ h₁ h₂
  · rw [hL]
    exact hU rfl V H hn t₁ f₂ f₂' φ φ' hT hu Y₁ Y₂ be₁ be₂ al₁ al₂ hY hb

end Top2

end Formalism.L2.SG.LsDatumA
