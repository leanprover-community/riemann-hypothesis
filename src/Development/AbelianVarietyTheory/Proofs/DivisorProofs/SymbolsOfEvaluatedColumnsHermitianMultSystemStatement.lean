module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystem
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

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.symbols_of_evaluated_columns_hermitianMultSystem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → ∀ l : Fin S.N → E, (∀ (a : Fin (S.T - S.D)) (α : MonoDeg (Fin S.D) a) (p : Fin δ), ∃ h : word Φ.mul (fun q k => join s l ((col (ix (⟨a, α⟩, p))).β q, k)) (Φ.ι (col (ix (⟨a, α⟩, p))).x) ∈ Φ.U a, ∀ α' p', Φ.sym a ⟨_, h⟩ (α', p') = if α'.1 = α.1 then (∑ k, l k * Φ.y p' k) ^ (S.T - a) * Φ.res (Φ.ι (m p)) p' else 0) ∧ ∀ k, k ∉ Set.range ix → (col k).j = S.D → word Φ.mul (fun q j => join s l ((col k).β q, j)) (Φ.ι (col k).x) ∈ Φ.U (S.T - S.D) := by
  first | exact @GlobalTheory.HSShort.symbols_of_columns | exact GlobalTheory.HSShort.symbols_of_columns | (intros; apply GlobalTheory.HSShort.symbols_of_columns <;> assumption)
