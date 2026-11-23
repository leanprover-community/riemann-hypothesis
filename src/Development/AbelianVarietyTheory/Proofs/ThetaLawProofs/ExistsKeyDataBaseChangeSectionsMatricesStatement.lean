module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataBaseChangeSectionsMatrices
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.exists_keyData_baseChange_sections_matrices : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (R' : Type) [CommRing R'] (f : O →+* R') (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → ∃ (x' : KeyIn R') (φ : x'.P.A.left ⟶ x.P.A.left) (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (s' : Fin x'.P.g → RR x' n) (b' : ∀ j, Fin ((l - j * n) ^ x'.P.g) → RR x' (l - j * n)) (m' : _), KeyVia x' x f φ w ∧ (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) ∧ (∀ j k, SecVia x' x φ w (b' j k) (b j (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)))) ∧ (∀ j ≤ x'.P.g, IsBasis x' (b' j)) ∧ IsMul x' l s' b' m' ∧ (∀ i j j' k k', m' i j j' k k' = f (m (i.cast hg) j j' (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)) (k'.cast (congrArg (fun r => (l - j' * n) ^ r) hg)))) ∧ (Finite (Sp R') → FinZ x s → FinZ x' s') := by
  first | exact @GlobalTheory.KeyBaseChangeData.exists_baseChange_data | exact GlobalTheory.KeyBaseChangeData.exists_baseChange_data | (intros; apply GlobalTheory.KeyBaseChangeData.exists_baseChange_data <;> assumption)
