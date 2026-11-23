module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullbackStatement
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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.cupZ_pull_apply_fv : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), (cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)).1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) = ψ (fv a E E' φ (z ≫ fst A B)) * fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
  intro R _ A B m₁ m₂ a b E _ _ E' _ _ E'' _ _ φ ψ z
  have e1 : fv (m₁.coef.pullbackOneCocycle a) E E' φ z = fv a E E' φ (z ≫ fst A B) := by
    rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback R A (A ⊗ B) (fst A B) m₁ a]; rfl
  have e2 : fv (m₂.coef.pullbackOneCocycle b) E' E'' ψ (spOver φ ≫ z) = fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
    rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback R B (A ⊗ B) (snd A B) m₂ b]; simp only [Fn1.pull, Category.assoc]
  rw [cupZ_apply]
  change ψ (fv (m₁.coef.pullbackOneCocycle a) E E' φ z) *
    fv (m₂.coef.pullbackOneCocycle b) E' E'' ψ (spOver φ ≫ z) = _
  rw [e1, e2]
