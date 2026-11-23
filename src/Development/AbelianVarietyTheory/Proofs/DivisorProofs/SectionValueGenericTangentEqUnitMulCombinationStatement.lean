module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigValD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericTangentEqUnitMulCombination
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
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.sectionValue_genericTangent_eq_unit_mul_combination : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C] (w₀ : GlobalTheory.UT.W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U w₀ ρ → ∀ (y : epsR R ⟶ G) (yA : Sp (DualNumber C) ⟶ (TFK (R := R) C ⊗ A.A).left), IsTangent y → VecAt U C y yA → ∀ (k : ℕ) (i₀ : A.L.ι) (jG : U.LG.L.ι), ⊤ ≤ (jFK (R := R) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → ∃ Θ : (DualNumber C)ˣ, (Θ : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigVal U.LG jG) ^ k = valR (jFK (R := R) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k ∧ ∀ (t : GlobalTheory.UT.SecA A C k) (σ' : U.SecGF C k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) C) A.A).left (U.genF C).left t (UnifPre.gFK (G := G) C) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → C) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) C) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) C) (fun i => scal (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left (c i)) → valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := R) C)).U fun _ => i₀) (t.f fun _ => i₀) = (Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) ((σ i).f fun _ => jG)) := by
  first | exact @GlobalTheory.MBLow.TanVal.value_tangent | exact GlobalTheory.MBLow.TanVal.value_tangent | (intros; apply GlobalTheory.MBLow.TanVal.value_tangent <;> assumption)
