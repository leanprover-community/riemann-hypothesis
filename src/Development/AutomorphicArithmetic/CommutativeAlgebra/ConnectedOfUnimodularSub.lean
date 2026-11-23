module

public import Mathlib.Data.Nat.Notation
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
public import Development.EtaleCohomology.EtaleSheaves.LeafChartRing
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory

variable (D : Type) [CommRing D] (d : ℕ)

private abbrev Sm (X : RF) (p : ℕ) (T : Scheme.{0}) : Type :=
  {x : Fin (p + 1) → X.obj Γ(T, ⊤) // ∀ i j, X.rel (x i) (x j)}

private theorem cond2 (p : ℕ) (T : Scheme.{0}) (a b : Sx (CN (L1 D d)) p T)
    (h : sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a =
      sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) b) :
    EtLoc T fun V k => sxRes k a = sxRes k b ∨ ∃ u : Sx (CN (L2 D d)) p V,
      sxMap (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)) u =
        sxRes k (sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a) := by
  have hab : a = b := by
    let a' : Sm (L1 D d) p T := a
    let b' : Sm (L1 D d) p T := b
    have h' : ∀ i, (a'.1 i).1 = (b'.1 i).1 := fun i => congrFun (congrArg Subtype.val h) i
    exact Subtype.ext (funext fun i => Subtype.ext (h' i))
  exact ⟨⊤, Scheme.etaleTopology.top_mem T, fun V k _ => Or.inl (by rw [hab])⟩

private theorem eqv_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine (Function.bijective_iff_has_inverse).2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

end UpperTheory
