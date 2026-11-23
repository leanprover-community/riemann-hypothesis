module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexCubeAbelianPointThetaFaceEqPartialSum
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralGaugeValuesAreValuationUnits
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def phiXY (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y : Fin g → ℂ) : (DegPre.BF D ℂ).left ⟶ (G3 D.P.A).left :=
  (lift (fst _ _ ≫ ν.eA (d.ex x)) (lift (fst _ _ ≫ ν.eA (d.ex y)) (snd _ _))).left

theorem ptB_phiXY (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) :
    ptB ν d z ≫ phiXY ν d x y = pt3 ν d x y z := by
  rw [ptB, phiXY, pt3, ← Over.comp_left, comp_lift, lift_fst_assoc, comp_lift, lift_fst_assoc, lift_snd,
    Category.id_comp, Category.id_comp]

theorem isOpen_and_differentiableOn_valF_pt3_cubW : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), Geo ν d → ∀ (x y : Fin g → ℂ) (j : thK → D.P.L.ι), IsOpen {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧ DifferentiableOn ℂ (fun z => valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} := by
  intro R _ _ D _ N g ν d G x y j
  have hs : {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} = {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ (phiXY ν d x y ⁻¹ᵁ cubW D j)} := by
    ext z
    simp only [Set.mem_setOf_eq, ← ptB_phiXY ν d x y z, Scheme.Hom.comp_preimage]
  obtain ⟨ho, hd⟩ := G.hol (phiXY ν d x y ⁻¹ᵁ cubW D j)
    (((phiXY ν d x y).appLE (cubW D j) (phiXY ν d x y ⁻¹ᵁ cubW D j) le_rfl).hom (D.cub.t.s j).val)
  rw [hs]
  refine ⟨ho, hd.congr fun z hz => ?_⟩
  have e := UnitVal.valF_appLE' (x := ptB ν d z) (phiXY ν d x y) (cubW D j) le_rfl hz (D.cub.t.s j).val
  rw [ptB_phiXY] at e
  exact e.symm

end GlobalTheory.MBLow.Cl.CubHol

end
