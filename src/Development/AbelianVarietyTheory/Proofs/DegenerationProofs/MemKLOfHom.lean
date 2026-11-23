module

public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory

theorem memKL_of_hom : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B), IsMonHom ψ → ∀ (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → LBIso L (M.pull ψ.left) → ∀ (T : Over S) (x : T ⟶ A), GlobalTheory.MemKL B M (x ≫ ψ) → GlobalTheory.MemKL A L x := by
  intro S A B _ _ ψ hψ L M hL hM hw T x hx
  obtain ⟨w, hw⟩ := hw
  replace hw := (isGen_iff w).1 hw
  intro p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  let U : T ⊗ A ⟶ T ⊗ B := lift (fst T A) (snd T A ≫ ψ)
  have k₁ : U ≫ fst T B = fst T A := lift_fst _ _
  have k₂ : U ≫ snd T B = snd T A ≫ ψ := lift_snd _ _
  have k₃ : U ≫ ((fst T B ≫ x ≫ ψ) * snd T B) = ((fst T A ≫ x) * snd T A) ≫ ψ := by
    rw [MonObj.comp_mul, k₂, ← Category.assoc, k₁, MonObj.mul_comp, Category.assoc]
  obtain ⟨n, hn⟩ : ∃ n : ((fst T A).left ⁻¹ᵁ V).toScheme ⟶ ((fst T B).left ⁻¹ᵁ V).toScheme,
      n ≫ ((fst T B).left ⁻¹ᵁ V).ι = ((fst T A).left ⁻¹ᵁ V).ι ≫ U.left :=
    ⟨IsOpenImmersion.lift _ (((fst T A).left ⁻¹ᵁ V).ι ≫ U.left) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q.left y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn M _ _ _) c hc
  let φ' : Fin 2 → (((fst T A).left ⁻¹ᵁ V).toScheme ⟶ A.left) := fun k => ((fst T A).left ⁻¹ᵁ V).ι ≫
    (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _) k
  obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame M (fun k => φ' k ≫ ψ.left) _ ![1, -1] n (fun k => by
    show (_ ≫ _) ≫ ψ.left = n ≫ _ ≫ _
    rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
    fin_cases k
    exacts [congrArg (fun q => _ ≫ q.left) k₃.symm, congrArg (fun q => _ ≫ q.left) k₂.symm])) c₁ h₁
  obtain ⟨c₃, h₃⟩ := exists_down hw hM hL c₂ h₂
  exact gen_chartPull (chartPullOut L _ _ _ φ' fun _ => rfl) c₃ h₃

end GlobalTheory
