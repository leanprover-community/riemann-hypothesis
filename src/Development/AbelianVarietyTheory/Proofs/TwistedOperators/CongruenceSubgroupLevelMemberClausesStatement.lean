module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceSubgroupLevelMemberClauses
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.congruenceSubgroup_level_member_clauses : ∀ (D : D7) (c : GlobalTheory.EvenOnto.Com D) (s : GlobalTheory.EvenOnto.PiLocalization₂ D) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ P.asIdeal → P.under (𝓞 D.host.F) ∈ c.S) → IsSelfDualC s.V s.Λ → s.J = Lev.levA s.V (congLev D.sp.cm s.V.gram s.Λ 𝔪) → s.J ≤ GfC s.V ∧ (∃ U : Subgroup (GA D s.V), IsOpen (U : Set (GA D s.V)) ∧ ∀ k ∈ U, k ∈ GfC s.V → k ∈ s.J) ∧ (∀ k ∈ s.J, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v) ∧ (∀ k ∈ GfC s.V, k ∈ GlobalTheory.EvenOnto.intOff c s → (∀ v ∈ c.S, GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k = 1) → k ∈ s.J) ∧ SphOff (s.J : Set (GA D s.V)) 1 c.S ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ s.J, ∃ k₁ ∈ s.J, ∃ k₂ ∈ s.J, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  first | exact @GlobalTheory.CongMember.congLev_clauses | exact GlobalTheory.CongMember.congLev_clauses | (intros; apply GlobalTheory.CongMember.congLev_clauses <;> assumption)
