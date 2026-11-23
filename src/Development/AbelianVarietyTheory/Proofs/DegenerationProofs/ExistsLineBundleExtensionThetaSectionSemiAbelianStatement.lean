module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleExtensionThetaSectionSemiAbelian
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

theorem _root_.GlobalTheory.T.exists_lineBundle_extension_thetaSection_semiAbelian : Semi.extend_existsSt.{0} → Out.MulNSt → (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), letI := L.grp; letI := L.comm; IsSemiAbelian C.GG → C.HasTests → C.TorsSec n → T.Few n → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  first | exact @GlobalTheory.ZJ.exists_extension_with_section | exact GlobalTheory.ZJ.exists_extension_with_section | (intros; apply GlobalTheory.ZJ.exists_extension_with_section <;> assumption)
