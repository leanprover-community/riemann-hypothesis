module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerBoundaryEtaleCohomology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_kummer_boundary_etale_cohomology : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ ∃ bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1, (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → ∀ (n : ℤ) x, pull _ f _ _ (bd E' n x) = bd E n (pull _ f _ _ x)) ∧ (∀ (E : Spc), Inv q E → ∀ n : ℤ, Function.Exact (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) n) (bd E n) ∧ Function.Exact (bd E n) (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) ∧ Function.Exact (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) (n + 1))) ∧ (∃ s : ℤˣ, ∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → bd (sch.obj X) 0 (secClass Gm (unitSec u)) = s • kum q u) ∧ ∃ s : ℤˣ, ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → bd E 1 (picClass L) = s • c1 q L := by
  first | (exact @GlobalTheory.kummer_boundary) | (exact GlobalTheory.kummer_boundary) | (intros; apply GlobalTheory.kummer_boundary <;> assumption)
