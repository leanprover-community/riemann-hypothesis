module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
noncomputable section
namespace GlobalTheory.MBLow.TrSec

variable {S : Scheme.{0}} (P : PolAV S)

lemma chart_le (j : Fin 1 → P.L.ι) :
    (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S)).U j ≤ (snd (baseOver S) P.A).left ⁻¹ᵁ P.L.U (j 0) :=
  LB.wchart_le P.L _ j 0

def thSec (s : P.L.Sec) : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S)) where
  f j := ReciprocityTheory.ChartRestriction.G.DVR.rs (chart_le P j) (((snd (baseOver S) P.A).left.app (P.L.U (j 0))).hom (s.f (j 0)))
  compat i j := by
    refine ReciprocityTheory.ChartRestriction.G.DVR.app_compat_generic (snd (baseOver S) P.A).left (chart_le P i) (chart_le P j)
      (s.f (i 0)) (s.f (j 0)) (P.L.g (i 0) (j 0)) (s.compat _ _) _ ?_
    simp only [LPow, LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
    rfl

lemma projectionPullbackSectionBaseProduct_isInverseImage (s : P.L.Sec) : IsPolAVSectionInverseImage P (baseOver S) s (thSec P s) := by
  intro i h
  rfl

lemma snd_inv (p : P.A.left) : (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) = p := by
  have e : (λ_ P.A).inv ≫ snd (baseOver S) P.A = 𝟙 P.A := (λ_ P.A).inv_hom_id
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
  rfl

lemma nonzero_thSec (s : P.L.Sec) (p : P.A.left) (hp : p ∈ nonzeroLocus s) :
    (λ_ P.A).inv.left.base p ∈ nonzeroLocus (thSec P s) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k, ?_⟩
  have hq : (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) = p := snd_inv P p
  show _ ∈ (baseOver S ⊗ P.A).left.basicOpen
    (((baseOver S ⊗ P.A).left.presheaf.map (homOfLE (chart_le P (fun _ => k))).op).hom
      (((snd (baseOver S) P.A).left.app (P.L.U k)).hom (s.f k)))
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
  refine ⟨?_, ?_⟩
  · show _ ∈ LB.wchart P.L _ _
    refine Set.mem_iInter.2 fun _ => ?_
    show (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) ∈ (P.L.U k : Set P.A.left)
    rw [hq]; exact P.A.left.basicOpen_le _ hk
  · show (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) ∈ P.A.left.basicOpen (s.f k)
    rw [hq]; exact hk

end GlobalTheory.MBLow.TrSec
