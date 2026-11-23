module

public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange
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
import Mathlib.RingTheory.Henselian
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH.SecImm
open GlobalTheory.Points GlobalTheory.ProjSpace

section
variable {o : Type} [CommRing o] {m m' : ℕ} {K : Type} [Field K] {Y : Scheme.{0}}

theorem crd_toProj {L : LB Y} (f : Y ⟶ Sp o) (s : Fin (m + 1) → L.Sec) (hs : ⨆ i, nonzeroLocus (s i) = ⊤)
    (x : Sp K ⟶ Y) (k : L.ι) (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    Crd (O1 o m) (coord o m) (x ≫ toProj f s hs) (fun i => valF x _ ((s i).f k)) := by
  obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top (x ≫ toProj f s hs) (iSup_chart o m)
  have hT : ⊤ ≤ x ⁻¹ᵁ (toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k) := fun z hz => ⟨hi hz, hk hz⟩
  have hu := (isUnit_resG_sec (s i) k (W := toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k)
    (inf_le_left.trans (toProj_preimage_chart f s hs i).le) inf_le_right).map (valMap x _ hT).hom
  rw [← valR_eq] at hu
  refine (LinFrame.crd_iff _ _).2 ⟨i, hu.unit, hi, fun j => ?_⟩
  have := congrArg (valR x _) (sec_eq_pullRatio_toProj_mul f s hs i j k
    (W := toProj f s hs ⁻¹ᵁ chart o m i ⊓ L.U k) inf_le_left inf_le_right)
  rw [valR_mul x _ hT, valR_res x _ hT, LinFrame.valR_pullRatio x _ _ hT] at this
  exact this.trans (mul_comm _ _)

end

end GlobalTheory.ZH.SecImm
