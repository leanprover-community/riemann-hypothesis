module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSharpBasisSharpBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ProductTorsionSectionBound
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.e8_prod_torsion_section_bound : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (gQ : ℕ) {S : Scheme.{0}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (hP : E8Fibration.IsProd pr) (N : ℕ) {T : Over S}
  (b : Fin gQ ⊕ Fin gQ → (T ⟶ B)), (∀ c, b c ^ N = 1) → ∀ (_hN : 0 < N := by assumption),
  (∀ i, E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ^ N = 1) ∧
  ∀ (act : Fin 2 → (A ⟶ A)), (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) → ∀ (a : Fin 2) (i : Fin (2 * (8 * gQ))),
    E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a =
      Out.linComb (fun i' => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1)))
        (fun i' => ((E8Fibration.Lab.labMat W hW.2 gQ a i' i : ZMod N)).val) := by
  exact @GlobalTheory.Poinc.Sep.E8Fibration.Lab.ptOf_torsion_and_act
