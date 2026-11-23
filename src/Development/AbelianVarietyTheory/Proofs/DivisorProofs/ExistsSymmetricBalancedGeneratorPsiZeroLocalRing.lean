module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPreDataLawsOfGeneratorValuesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedBimultiplicativeGeneratorLambdaInvStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiGeneratorsDegenerationLawsSymmetricBalaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTrivialisationOfBalancedBimultiplicativStatement
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

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UTau0

theorem exists_symmetric_balanced_generator_psi_zero_localRing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ : DegPre R) (O : Type) [CommRing O]
    [StarRing O] [Module O D₀.X] [Module.Projective O D₀.X] [Module.Finite O D₀.X] (onB : D₀.P.OAct O),
    (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) → ∀ w0 : O, w0 + star w0 = 1 →
    (∃ u : LB.Gen (LB.LinComb D₀.P.L (K := Fin 4) ![(padd D₀.P.A (𝟙 _) (onB.act w0)).left, 𝟙 D₀.P.A.left,
        (onB.act w0).left, (toUnit D₀.P.A ≫ η[D₀.P.A]).left] ![1, -2, -1, 2]),
      u.IsGen ∧ LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ u (eSec D₀.P.A)) (LB.oneGen D₀.P.L)) →
    ∃ (ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => ptK (D₀.c y)) (fun _ => -1)))
      (h : ∀ y, (ψ y).IsGen),
      letI : Module O ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).X := ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).OAct O, oa.onB = onB ∧
        ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := ψ, psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := ψ, psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := ψ, psi_gen := h } : DegPre R) y Set.univ := by
  intro R _ _ _ D₀ O _ _ _ _ _ onB hlin w0 hw ⟨uw, huw, huw0⟩
  have cadd : ∀ y y' : D₀.X, D₀.c (y + y') = D₀.c y * D₀.c y' := fun y y' => D₀.c_add y y'
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_balanced_bimultiplicative_generator_lambda_inv R D₀.P.A D₀.P.isAb ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub O onB.toRingAct
    onB.rosati D₀.X D₀.c cadd hlin
  obtain ⟨τ', hτ', hτs⟩ := GlobalTheory.T.symmetric_trivialisation_of_balanced_bimultiplicative R D₀.P.A D₀.P.isAb ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub O
    onB.toRingAct onB.rosati D₀.X D₀.c cadd hlin w0 hw τ hτ
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_psi_generators_degenerationLaws_symmetricBalanced R D₀ O onB hlin w0 hw uw huw huw0 τ' hτ' hτs
  obtain ⟨h, rest⟩ := GlobalTheory.T.degenerationPreData_laws_of_generator_values R D₀ O onB hlin w0 uw huw huw0 ψ hψ
  exact ⟨_, h, rest⟩

end GlobalTheory.UTau0
