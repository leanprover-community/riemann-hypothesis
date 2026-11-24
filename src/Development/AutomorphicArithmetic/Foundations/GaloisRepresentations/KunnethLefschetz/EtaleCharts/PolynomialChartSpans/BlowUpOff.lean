module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.Gal.KunnethLefschetz.G.blOff :
    UpperTheory.Gal.KunnethLefschetz.G.BlowUpOff := by
  intro R _ _ Z W _ _ π hπ
  have hdg : IsClosedImmersion (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)) := by
    change IsClosedImmersion (pullback.diagonal (Over.hom Z))
    infer_instance
  have hft : LocallyOfFiniteType (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) := by
    change LocallyOfFiniteType (pullback.fst (Over.hom Z) (Over.hom Z) ≫ Over.hom Z)
    infer_instance
  have hln : IsLocallyNoetherian (Over.left (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))
  have hsupp : ((Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).support : Set _) =
      Set.range (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)) := by
    rw [Scheme.Hom.support_ker]
    exact (Scheme.Hom.isClosedEmbedding (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).isClosed_range.closure_eq
  refine ⟨FunctorialResolution.Blowup.isProper_of_isBlowupAlongIdealSheaf hπ, ?_, ?_⟩
  · change IsClosedImmersion (pullback.fst (Over.Hom.left π) (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)))
    infer_instance
  · intro U hU
    have hUeq : U = (Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).support.compl := by
      apply SetLike.coe_injective
      rw [hU]
      simp [hsupp]
    subst hUeq
    refine ⟨FunctorialResolution.Blowup.blowupIsIsoOffCenter _ _ _ _ hπ, ?_⟩
    change _ = (Set.range (pullback.fst (Over.Hom.left π) (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))))ᶜ
    rw [Scheme.Pullback.range_fst]
    simp [hsupp]
