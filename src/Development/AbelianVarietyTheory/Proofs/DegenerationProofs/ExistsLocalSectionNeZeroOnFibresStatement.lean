module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalSectionNeZeroOnFibres
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_local_section_ne_zero_on_fibres' : ∀ (C : Core) (L : C.Law) (T : C.Theta) (Om : Set C.G.toScheme) (ν), IsOpen Om → T.Norms Om ν → L.CompanionTheory Om → (∃ (M : LB C.G.toScheme) (w : LB.Iso (M.pull C.a) T.L.L) (D : M.ι → C.A.left.Opens), M.IsLB ∧ w.IsGen ∧ (∀ i, (D i : Set C.A.left).Nonempty) ∧ ∀ (p : ℕ) [Fact p.Prime] (x : Sp (PadicAlgCl p) ⟶ C.A.left) (i : M.ι) (j : T.L.L.ι), IntAt C.a (M.U i) x → Set.range x ⊆ T.L.L.U j → Set.range x ⊆ D i → ‖valF x _ (w.s (j, fun _ => i)).val‖ * ν p x j = 1) → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  first | exact @GlobalTheory.exists_local_section_ne_zero_on_fibres | exact GlobalTheory.exists_local_section_ne_zero_on_fibres | (intros; apply GlobalTheory.exists_local_section_ne_zero_on_fibres <;> assumption)
