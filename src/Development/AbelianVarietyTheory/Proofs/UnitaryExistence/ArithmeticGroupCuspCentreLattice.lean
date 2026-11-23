module

public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankRatSkewHermitianMatricesCmFieldStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SkewMatrixMultipleInLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SpanCuspCentreArithmeticGroupFgStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZMatEInjective
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

theorem exists_int_basis_of_fg {V : Type} [AddCommGroup V] [Module ℚ V] (Z : Submodule ℤ V)
    (hZ : Z.FG) {n : ℕ} (hn : Module.finrank ℚ (Submodule.span ℚ (Z : Set V)) = n) :
    ∃ bs : Fin n → V, LinearIndependent ℤ bs ∧ Submodule.span ℤ (Set.range bs) = Z := by
  haveI : Module.Finite ℤ Z := Module.Finite.iff_fg.2 hZ
  haveI : HasUniqueDiv V := HasUniqueDiv.of_module_rat V
  haveI : Module.Free ℤ Z := inferInstance
  let b := Module.finBasis ℤ Z
  have hli : LinearIndependent ℤ (Z.subtype ∘ b) :=
    b.linearIndependent.map' Z.subtype Z.ker_subtype
  have hsp : Submodule.span ℤ (Set.range (Z.subtype ∘ b)) = Z := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hq : LinearIndependent ℚ (Z.subtype ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hli
  have h1 := finrank_span_eq_card hq
  have h2 : Submodule.span ℚ (Set.range (Z.subtype ∘ b)) = Submodule.span ℚ (Z : Set V) := by
    conv_rhs => rw [← hsp]
    rw [Submodule.span_span_of_tower]
  rw [h2, hn, Fintype.card_fin] at h1
  subst h1
  exact ⟨_, hli, hsp⟩

theorem latZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (Comp : Type) (X : Comp → Data E r), FJ.LatZ X ρ := by
  intro E _ _ _ r ρ Comp X cu
  obtain ⟨c, cu⟩ := cu
  have hZ : (Submodule.span ℤ (FJ.zGam (X c) cu) : Set (Matrix (Fin ρ) (Fin ρ) E)) =
      FJ.zGam (X c) cu := by
    have := Submodule.span_eq (AddSubgroup.toIntSubmodule (zGamSub (X c) cu))
    exact congrArg (fun S : Submodule ℤ (Matrix (Fin ρ) (Fin ρ) E) =>
      (S : Set (Matrix (Fin ρ) (Fin ρ) E))) this
  have hdim := GlobalTheory.T.finrank_rat_skewHermitian_matrices_cmField E ρ (X c).Ψ (X c).cmType
    (Submodule.span ℚ (Submodule.span ℤ (FJ.zGam (X c) cu) : Set (Matrix (Fin ρ) (Fin ρ) E))) (by
      rw [hZ]
      intro β
      constructor
      · intro h
        induction h using Submodule.span_induction with
        | mem x hx => exact hx.1
        | zero => intro a b; simp [cc_zero']
        | add x y _ _ hx hy =>
          intro a b
          rw [Matrix.add_apply, Matrix.add_apply, cc_add', hx, hy]; ring
        | smul q x _ hx =>
          intro a b
          have hq : cc (q : E) = q := by simp [cc]
          rw [Matrix.smul_apply, Matrix.smul_apply, Rat.smul_def, Rat.smul_def, cc_mul', hq, hx]
          ring
      · intro h
        obtain ⟨n, hn, hm⟩ := GlobalTheory.T.skew_matrix_multiple_in_lattice E r ρ (X c) cu β h
        have h1 := Submodule.smul_mem (Submodule.span ℚ (FJ.zGam (X c) cu)) ((n : ℚ)⁻¹)
          (Submodule.subset_span hm)
        rwa [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'),
          one_smul] at h1)
  obtain ⟨bs, h1, h2⟩ := exists_int_basis_of_fg _ (GlobalTheory.T.span_cuspCentre_arithmeticGroup_fg E r ρ (X c) cu) hdim
  refine ⟨bs, h1, fun β => ?_⟩
  exact ((Set.ext_iff.1 hZ β).symm).trans (SetLike.ext_iff.1 h2 β).symm

end GlobalTheory.CuspCentre
