module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

theorem lbIso_sec_onto : ∀ (X : Scheme.{0}) (A B : LB X) (w : LB.Iso A B), A.IsLB → B.IsLB → w.IsGen →
    ∀ b : B.Sec, ∃ a : A.Sec, SecMaps w a b := by
  intro X A B w hA hB hw b
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfIso b hw hA hB, fun p => ?_⟩
  obtain ⟨p, q⟩ := p
  have hV : B.U p ⊓ A.U q ≤ A.U q ⊓ B.U p := fun _ h => ⟨h.2, h.1⟩
  have e := congrArg (ReciprocityTheory.ChartRestriction.G.DVR.rs hV) (ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec b hw hA hB q p)
  rw [ReciprocityTheory.ChartRestriction.G.DVR.isoCand_rs] at e
  have hs : res (hV.trans (ReciprocityTheory.ChartRestriction.G.DVR.divLe (A := A) (B := B) q p)) (w.s (p, q)) = w.s (p, q) :=
    Units.ext (GlobalTheory.Cartier.resG_self _ _)
  rw [hs] at e
  have e2 : resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) ((ReciprocityTheory.ChartRestriction.G.DVR.secOfIso b hw hA hB).f q) =
      (((w.s (p, q))⁻¹ : Γ(X, B.U p ⊓ A.U q)ˣ) : Γ(X, B.U p ⊓ A.U q)) * resG X inf_le_left (b.f p) := by
    refine Eq.trans ?_ e
    exact (GlobalTheory.Cartier.resG_resG _ _ _).symm
  change resG X inf_le_left (b.f p) = ((@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)ˣ) : Γ(X, B.U p ⊓ A.U q)) * _
  simp only [id]
  rw [e2]
  exact (Units.mul_inv_cancel_left _ _).symm

end GlobalTheory.MBLow
