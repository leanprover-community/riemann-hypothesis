module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeTranslateOfMemSpanFixedTranslates
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalThetaInertPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

@[expose] public section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_hecke_translate_of_mem_span_fixed_translates : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (s w : M), (∀ k ∈ K, ρ k s = s) → (∀ k ∈ K, ρ k w = w) → w ∈ Submodule.span ℂ (Set.range fun g => ρ g s) → ∃ h ∈ Hecke ℂ K, heckeVec ρ K h s = w := by
  first | exact @GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span | exact GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span | (intros; apply GlobalTheory.SphTheta.AvgHecke.exists_hecke_of_mem_span <;> assumption)
