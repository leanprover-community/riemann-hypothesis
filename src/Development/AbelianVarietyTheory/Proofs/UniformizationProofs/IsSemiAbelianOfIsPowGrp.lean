module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsMonHomOfComm
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPowGrpBaseChange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowExt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.QuasiCompactGeomConnectedPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiPow

theorem nonempty_torusExtension {K : Type} [Field K] {G' G : Over (Spec (CommRingCat.of K))} [GrpObj G'] [GrpObj G]
    {j : ℕ} (p : IsPowGrp G' G j) (E : TorusExtension G) : Nonempty (TorusExtension G') := by
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  letI := E.grpB
  obtain ⟨pT, -⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Spec (CommRingCat.of K)) E.X (Fin j → E.X) j (AddEquiv.refl _)
  obtain ⟨q', hq, hq1, hq2, hq3, hq4, -⟩ :=
    GlobalTheory.PowMap.main _ G' G (powObj E.B j) E.B j p (powIsPowGrp E.B j) E.q
  obtain ⟨i', hi, hi1, -⟩ := GlobalTheory.PowMap.main _ _ _ G' G j pT p E.i
  exact ⟨{ X := Fin j → E.X
           B := powObj E.B j
           isAbelian := (GlobalTheory.PowGrp.powers _ _ _ j (powIsPowGrp E.B j)).2.2.2.1 E.isAbelian
           q := q'
           q_hom := hq1 E.q_hom
           q_flat := hq2 E.q_flat
           q_surjective := hq3 E.q_surjective
           q_quasiCompact := hq4 E.q_quasiCompact
           i := i'
           i_hom := hi1 E.i_hom
           isKernel := GlobalTheory.PowKernel.main _ _ _ _ _ _ _ j pT p (powIsPowGrp E.B j) E.i E.q i' q' hi hq
             E.isKernel }⟩

theorem isSemiAbelian_of_isPowGrp : ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (j : ℕ) (_ : IsPowGrp G' G j), IsSemiAbelian G → IsSemiAbelian G' := by
  intro S G G' _ _ j p hG
  obtain ⟨h1, h2, -, -, h5⟩ := GlobalTheory.PowGrp.powers S G' G j p
  have hq := GlobalTheory.PowGrp.quasiCompact_geomConnected_pow S G' G j p
  refine ⟨h5 hG, h1 hG.smooth, h2 hG.separated, hq.1 hG.quasiCompact, hq.2 hG.smooth hG.geomConnected,
    fun Ω _ _ f => ?_⟩
  obtain ⟨p', -⟩ := GlobalTheory.isPowGrp_baseChange S _ f G' G j p
  obtain ⟨E⟩ := hG.fibres Ω f
  exact nonempty_torusExtension p' E

end GlobalTheory.SemiPow
