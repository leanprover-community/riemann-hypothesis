module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTraitUniformisationLatticePowEight
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc Formalism.L2.Pj

theorem _root_.GlobalTheory.T.eighthPower_trait_uniformisation_lattice_pow_eight : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P T.y ε → ∃ (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G'), IsSemiAbelian G' ∧ ∃ (D' : DegData T.V (maximalIdeal T.V)) (U' : Unif (maximalIdeal T.V) D' P G') (j : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ y, ∃ v : T.Vˣ, PsiCoord D'.toPre y (v * T.ϖ ^ (qW W T.β (j y)).toNat)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing T.V) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x x' : TFK (R := T.V) K ⟶ P.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' x' → x' = x ≫ ε E → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) := by
  first | exact @GlobalTheory.EighthTorsion.main | exact GlobalTheory.EighthTorsion.main | (intros; apply GlobalTheory.EighthTorsion.main <;> assumption)
