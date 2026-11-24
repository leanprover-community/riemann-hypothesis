module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEtaleHasHeckeQuotientNoetherianDomain
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
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

theorem _root_.GlobalTheory.T.exists_etale_hasHeckeQuotient_noetherian_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] (s : Sp R ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over (Sp R)) ⟶ o.t.G)) (K : Set o.t.G.left) (q : Sp R), 1 ≤ D.p + D.q → admitted l 𝔓 p → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → ∃ (R' : Type) (_ : CommRing R') (π : Sp R' ⟶ Sp R) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π), Etale π ∧ q ∈ Set.range π ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K) := by
  first | exact @GlobalTheory.exists_etale_hasQuot_of_lists | exact GlobalTheory.exists_etale_hasQuot_of_lists | (intros; apply GlobalTheory.exists_etale_hasQuot_of_lists <;> assumption)
