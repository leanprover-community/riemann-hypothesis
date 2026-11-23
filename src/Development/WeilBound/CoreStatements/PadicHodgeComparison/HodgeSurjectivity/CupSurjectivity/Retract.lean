module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateFromSandwich
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictlySemistableChartAtOfSmoothStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace Sp spMap IsProjOver)

def retractPt (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    Spec (CommRingCat.of (OK l K)) ⟶ PSpace (OK l K) 2 :=
  GlobalTheory.ProjSpace.pt (RingHom.id (OK l K)) (fun _ => 1)
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one)

theorem retractPt_str (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    retractPt l K ≫ PSpace.str (OK l K) 2 = 𝟙 _ := by
  have hstr : ∀ (v : Fin (2 + 1) → OK l K) (hv : Ideal.span (Set.range v) = ⊤),
      GlobalTheory.ProjSpace.pt (RingHom.id (OK l K)) v hv ≫ PSpace.str (OK l K) 2 =
        spMap (RingHom.id (OK l K)) := by
    intro v hv
    rw [GlobalTheory.ProjSpace.pt, PSpace.str, GlobalTheory.ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C _ v r
  rw [retractPt, hstr]
  simp [spMap]

theorem retract_pf : Retract := by
  intro l _ K _ M d hM hd
  let N : Model l K := ⟨pullback M.p (PSpace.str (OK l K) 2), pullback.fst _ _ ≫ M.p⟩
  have h2 : SmoothOfRelativeDimension 2 (pullback.fst M.p (PSpace.str (OK l K) 2)) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 2)
    MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension 2) _ _
      (GlobalTheory.Adelic.smoothOfRelativeDimension_pspace _ 2)
  have hN : SmoothOfRelativeDimension (d + 1 + 1) N.p := by
    have := h2
    have := hd
    have : SmoothOfRelativeDimension (2 + d) (pullback.fst M.p (PSpace.str (OK l K) 2) ≫ M.p) :=
      smoothOfRelativeDimension_comp 2 d _ _
    rw [show d + 1 + 1 = 2 + d by omega]
    exact this
  have hsm : Smooth N.p := SmoothOfRelativeDimension.smooth (d + 1 + 1) N.p
  obtain ⟨⟨hproj, ϖ, hϖ, -⟩, -⟩ := hM
  refine ⟨N, pullback.fst _ _, pullback.lift (𝟙 _) (M.p ≫ retractPt l K) ?_, rfl, pullback.lift_fst _ _ _,
    ⟨⟨?_, ϖ, hϖ, ?_⟩, hsm⟩, hN⟩
  · rw [Category.assoc, retractPt_str, Category.comp_id, Category.id_comp]
  · exact GlobalTheory.ProjSpace.isProjOver_pullback hproj (GlobalTheory.ProjSpace.isProjOver_pspace_str _ 2)
  · intro x
    exact GlobalTheory.T.hasStrictlySemistableChartAt_of_smooth _ ϖ N.X N.p ⊤ x trivial inferInstance

end CrystallineSemistableComparison.Onto

end
