module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigenOfLocalComponentsFiniteAdelicPair
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eigen_of_local_components_finiteAdelic_pair : ∀ (D : D7) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), (∀ w, Continuous fun p : GA D S × GA D T => om p f w) → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) (s : HeightOneSpectrum (𝓞 D.host.F) → ℂ), (∀ v, v ∉ A → s v = 1) → (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (g' : GA D S) (h' : GA D T), Formalism.L2.Theta.mt S g' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt S g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → Formalism.L2.Theta.mt T h' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt T h + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → om (g', h') f = s v • f) → om (g, h) f = (∏ v ∈ A, s v) • f := by
  first | exact @GlobalTheory.PlaceProduct.eigen_of_local_components | exact GlobalTheory.PlaceProduct.eigen_of_local_components | (intros; apply GlobalTheory.PlaceProduct.eigen_of_local_components <;> assumption)
