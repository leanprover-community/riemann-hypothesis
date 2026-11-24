module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExpansionCoefMemAdicPow
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

theorem _root_.GlobalTheory.T.expansionCoef_mem_adic_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), U.ExpT (𝟙_ _) 1 σ f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ e : ℕ, ∃ s : Finset D.X, ∀ χ ∉ s, ∀ (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (b : R), Coef D χ u th (f χ) b → b ∈ I ^ (e + 1) := by
  first | exact @GlobalTheory.PsiRing.coef_mem_pow | exact GlobalTheory.PsiRing.coef_mem_pow | (intros; apply GlobalTheory.PsiRing.coef_mem_pow <;> assumption)
