module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistOfSeedCharacterPowers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.goodTwist_of_seed_character_powers : ∀ (D₁ D₂ D₃ : D7) (A : D₁.ntw.Tw → Finset (PlE D₁.host)) (σ : Seed D₁ A) (C₂ : NChoice D₂) (C₃ : NChoice D₃) (xd : ThData D₃) (u : D₃.what₂.places.Pl → D₁.what₂.places.Pl), SameExport D₁ D₂ → Kept C₂ C₃ → avPrimes D₂ = avPrimes D₃ → D₂.what₂.places.Pl = D₃.what₂.places.Pl → XdAll xd → (∀ i, avD D₁ (avDesign D₁) i ⊆ A i) → (∀ v₂ v₃, HEq v₂ v₃ → TwistedAt D₃ v₃ → TwistedAt D₁ (u v₃) ∧ ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (σ.s (u v₃))) ∧ HEq (rawPack C₂ v₂) (GlobalTheory.HeightCounting.twPackPow D₁ a (σ.pack (u v₃)))) → GoodO D₃ C₃ xd := by
  first | exact @GlobalTheory.HeightCounting.Up.GoodPrimeSelection.goodO_of_seed | exact GlobalTheory.HeightCounting.Up.GoodPrimeSelection.goodO_of_seed | (intros; apply GlobalTheory.HeightCounting.Up.GoodPrimeSelection.goodO_of_seed <;> assumption)
