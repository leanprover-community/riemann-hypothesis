module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiGeneratorsDegenerationLawsSymmetricBala
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_psi_generators_degenerationLaws_symmetricBalanced : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ w0 : O, w0 + star w0 = 1 → ∀ uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ τ' : ∀ y z : D₀.X, LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.PolDeg.lamPts (D₀.c y) (D₀.c z)) GlobalTheory.PolDeg.negε),
    GlobalTheory.UTau0.BalTau ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub onB.toRingAct D₀.c τ' →
    (∀ y z p J, Good D₀.P.L p J → val (τ' y z) (𝟙 _) p J = val (τ' z y) (𝟙 _) p J) →
    ∃ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
      GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ := by
  first | exact @GlobalTheory.UTau0.exists_psi_rLaws | exact GlobalTheory.UTau0.exists_psi_rLaws | (intros; apply GlobalTheory.UTau0.exists_psi_rLaws <;> assumption)
