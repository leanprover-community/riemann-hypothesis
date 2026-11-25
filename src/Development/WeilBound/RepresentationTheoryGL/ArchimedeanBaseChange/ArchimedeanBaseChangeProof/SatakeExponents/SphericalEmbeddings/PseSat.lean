module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.StageLift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSatakeParameterOfIsSubquotientOfInjective
import GroundTheory.LocalFields.LocalFourierHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory

namespace PositivityTheory.Rg.BcB.N3.PseSat

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem injective_of_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (hi : π.IsIrreducible) (f : π.IntertwiningMap σ)
    (hf : f ≠ 0) : Function.Injective f := by
  have := hi
  exact (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf

theorem isSubquotient_of_injective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (f : π.IntertwiningMap σ) (hf : Function.Injective f) :
    IsSubquotient π σ :=
  IsSubquotient.of_injective f hf

theorem satPerm : SatPerm k := by
  intro n ξ η V _ _ π hs hi hsph hq ⟨f, hf⟩
  have hinj := injective_of_ne_zero hi f hf
  have hq' := isSubquotient_of_injective f hinj
  borelize (GL (Fin n) k)
  have h1 := GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) ξ hq (μ := Measure.haar)
  have h2 := GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) η hq' (μ := Measure.haar)
  have hK := (GlobalTheory.CompanionTheory.SphSupp.isSpherical_iff_fixedVectors π).1 hsph
  exact GroundTheory.Automorphic.Spherical.satakeParameter_unique hK h1 h2

end PositivityTheory.Rg.BcB.N3.PseSat
