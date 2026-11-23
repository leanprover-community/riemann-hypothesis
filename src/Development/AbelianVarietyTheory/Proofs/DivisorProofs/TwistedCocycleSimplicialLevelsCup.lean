module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFrameFunctionCompare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc

theorem _root_.GlobalTheory.T.twisted_cocycle_simplicial_levels_cup : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ (a : ℕ) (j : Fin N), CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ)) (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀), ∀ p ≤ (0 : ℤ), ∃ ψ : ∀ m, (∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) → CohomologyClass ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m, (∀ m, Function.Bijective (ψ m)) ∧ ∀ n m, n + p = m → ∀ α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)), (∀ j c r hr, p < c → (α j).v c r hr = 0) → ∀ (a : ∀ j : Fin N, Cocycle (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (b : Cocycle ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m), (∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X p) ≫ (a j).1.v 0 r hr = (α j).v p r hr') → (∀ (k t : ℤ) (h : p + k = t) r hr hr', b.1.v k r hr = (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) p k t h ≫ (phi q V ℓ i (fun j => (z j).1) n α).v t r hr') → ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
  first | (exact @GlobalTheory.PBFg.graded_bijective) | (exact GlobalTheory.PBFg.graded_bijective) | (intros; apply GlobalTheory.PBFg.graded_bijective  <;> assumption)
