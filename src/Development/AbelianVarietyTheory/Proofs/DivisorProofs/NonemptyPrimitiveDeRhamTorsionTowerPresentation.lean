module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveStructureOfPrimitiveDeRhamClassStatement
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

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem exists_sub_tower {B : ℕ → Type} [∀ n, AddCommGroup (B n)] (r : ∀ n, B (n + 1) → B n)
    (hr : ∀ n, Function.Surjective (r n)) (a : ∀ n, B n) :
    ∃ h : ∀ n, B n, ∀ n, a n = h n - r n (h (n + 1)) := by
  choose s hs using hr
  refine ⟨fun n ↦ Nat.rec (motive := B) 0 (fun n x ↦ s n (x - a n)) n, fun n ↦ ?_⟩
  simp only [hs, sub_sub_cancel]

theorem nonempty_dat (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) : Nonempty (Dat t c) := by
  obtain ⟨f, hf⟩ := CatCoh.H1.mk_surjective _ c.1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_additiveStructure_of_primitiveDeRhamClass R A f (by rw [hf]; exact c.2)
  obtain ⟨h, hh⟩ := exists_sub_tower (B := fun n ↦ G.A n) (fun n ↦ G.res n) (fun n ↦ G.res_surjective n)
    (fun n ↦ fv f (G.A (n + 1)) (G.A n) (G.res n : G.A (n + 1) →ₐ[R] G.A n) (t.y (n + 1)))
  exact ⟨⟨f, hf, g, hg, h, hh⟩⟩

end GlobalTheory.PtExt
