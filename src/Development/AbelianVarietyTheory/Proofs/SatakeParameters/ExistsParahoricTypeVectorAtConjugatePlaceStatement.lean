module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_parahoricType_vector_at_conjugate_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → GlobalTheory.SplitWeil.IsTame μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = (μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k))⁻¹) → ∀ u : W, u ≠ 0 → (∀ g h : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → h.val = (g⁻¹).val.transpose → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom h) u = ((ξ d : ℂˣ) : ℂ) • u) → ∃ u' : W, u' ≠ 0 ∧ GlobalTheory.ThetaGL.IsParahoricVec μ π u' := by
  first | exact @GlobalTheory.ConjParahoric.exists_parahoricVec | exact GlobalTheory.ConjParahoric.exists_parahoricVec | (intros; apply GlobalTheory.ConjParahoric.exists_parahoricVec <;> assumption)
