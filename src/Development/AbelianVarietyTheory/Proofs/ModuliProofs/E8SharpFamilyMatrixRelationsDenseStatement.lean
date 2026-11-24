module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpFamilyMatrixRelationsDense
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
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.dense_fromSet_sharpClass : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j' j'', a j'' = a j * a j' → t.act j'' = t.act j' ≫ t.act j) ∧ (∀ j j' j'', a j'' = a j + a j' → t.act j'' = t.act j * t.act j') ∧ (∀ j, a j = 1 → t.act j = 𝟙 t.A) ∧ ∀ j i, t.pt i ≫ t.act j = (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod := by
  first | exact @GlobalTheory.sharp_family_relations | exact GlobalTheory.sharp_family_relations | (intros; apply GlobalTheory.sharp_family_relations <;> assumption)
