module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

noncomputable section

namespace GlobalTheory.CoveringCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Fibres

def SplitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (x : S) (k : Type) [Field k] [Algebra (S.residueField x) k] :
    Prop :=
  ∃ T : SplitExt (Sp k), T.IsGt ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) k)) ≫ S.fromSpecResidueField x)).obj G)

theorem splitOver_of_torusExtension {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) (k : Type)
    [Field k] [Algebra (S.residueField x) k]
    (h : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap (S.residueField x) k))).obj
      ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)))) :
    SplitOver G x k := by
  obtain ⟨T⟩ := h
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    ((isGrpPullback_pullback ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)
      (spMap (algebraMap (S.residueField x) k))).comp (isGrpPullback_pullback G _))
    (isGrpPullback_pullback G _)
  have := hG.comm
  exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T⟩

theorem exists_finite_splitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (S.residueField x) k),
      FiniteDimensional (S.residueField x) k ∧ SplitOver G x k := by
  have h₀ := IsSemiAbelian.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x) G hG
  have := h₀.smooth
  obtain ⟨k, hk, T⟩ := exists_finite_torusExtension (S.residueField x) (AlgebraicClosure (S.residueField x)) _
    inferInstance h₀.quasiCompact h₀.separated (h₀.fibres _ _)
  exact ⟨k, inferInstance, inferInstance, hk, splitOver_of_torusExtension G hG x k T⟩

end Fibres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section One

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end One

end GlobalTheory.CoveringCompare
