module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem relAmple_of_finite_etale_isogeny : ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ ψ : A ⟶ B, IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → ∀ (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → LBIso L (M.pull ψ.left) → Out.RelAmple A L → Out.RelAmple B M := by
  intro k _ _ A B _ _ hA hB ψ _ hf he hs L M hL hM hiso hamp
  have hN : IsLocallyNoetherian (Sp k) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of k)))
  have h₁ := (GlobalTheory.relAmple_finite_pow_iso (Sp k) A A (𝟙 A) L 1 one_pos hA hA hL
    (by simpa using (inferInstance : IsFinite (𝟙 A.left)))).2.2.2 (M.pull ψ.left) (LB.isLB_pull hM ψ.left) hiso hamp
  exact (GlobalTheory.relAmple_finite_pow_iso (Sp k) A B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs h₁

end GlobalTheory.SS
