module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem abelianScheme_id_pow_finite_etale_surjective :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (m : ℕ), IsAbelianScheme A → IsUnit (m : Γ(S, ⊤)) → IsMonHom ((𝟙 A) ^ m) ∧ IsFinite ((𝟙 A) ^ m).left ∧ Etale ((𝟙 A) ^ m).left ∧ Surjective ((𝟙 A) ^ m).left := by
  intro S A _ m hA hm
  obtain ⟨⟩ := hA
  have hmon : ∀ n : ℕ, IsMonHom ((𝟙 A) ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Hom.one_def]; infer_instance
    | succ n ih => rw [pow_succ, Hom.mul_def]; infer_instance
  have hfin : IsFinite ((𝟙 A) ^ m).left := GrpTangent.isFinite_id_pow A hm
  have het : Etale ((𝟙 A) ^ m).left := GrpTangent.etale_id_pow A hm
  refine ⟨hmon m, hfin, het, ⟨fun x => ?_⟩⟩
  set f := ((𝟙 A) ^ m).left with hf

  have hcl : IsClopen (Set.range f) :=
    ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩

  have hw : A.hom (f x) = A.hom x := by
    rw [← Scheme.Hom.comp_apply, hf, Over.w]

  have hsub : A.hom ⁻¹' {A.hom x} ⊆ Set.range f :=
    (A.hom.isConnected_preimage_singleton (A.hom x)).isPreconnected.subset_isClopen hcl
      ⟨f x, by simp [hw], Set.mem_range_self x⟩
  exact hsub rfl

end GlobalTheory
