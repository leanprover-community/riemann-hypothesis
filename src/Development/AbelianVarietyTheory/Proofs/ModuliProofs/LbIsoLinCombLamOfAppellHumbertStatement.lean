module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoLinCombLamOfAppellHumbert
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem _root_.GlobalTheory.T.lbIso_linComb_lam_of_appellHumbert_alt : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (P₀ : Out.PolAV (Sp ℂ)) (u₀ : HolUnif P₀.A P₀.L P₀.g) (H₀ : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ₀ : u₀.Λ → ℂ) (pr : Fin 8 → (P.A ⟶ P₀.A)) (R : Fin 8 → ((Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ))), u.IsAH Hm χ → u₀.IsAH H₀ χ₀ → (∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i) → (∀ z w, hermForm Hm z w = ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm H₀ (R i z) (R j w)) → (∀ l : u.Λ, χ l = Complex.exp (Real.pi * Complex.I * ∑ i, ∑ j, (W i j : ℂ) * ((hermForm H₀ (R i l) (R j l)).im : ℂ))) → LBIso P.L (LB.LinComb (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  first | exact @GlobalTheory.lbIso_linComb_lam_of_appellHumbert | exact GlobalTheory.lbIso_linComb_lam_of_appellHumbert | (intros; apply GlobalTheory.lbIso_linComb_lam_of_appellHumbert <;> assumption)
