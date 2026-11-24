module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergEpsilonTransport
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.rankin_selberg_epsilon_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle), (∀ x, ψ' (i x) = ψ x) → ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) k)) (π' : IrrRep (GL (Fin (m + 1)) k')) (τ : IrrRep (GL (Fin m) k)) (τ' : IrrRep (GL (Fin m) k')) (c : ℂ), RepRel i (cls π) (cls π') → RepRel i (cls τ) (cls τ') → HasPairEps ψ π.ρ τ.ρ c → HasPairEps ψ' π'.ρ τ'.ρ c := by
  first | exact @GlobalTheory.LocLanglands.hasPairEps_transport | exact GlobalTheory.LocLanglands.hasPairEps_transport | (intros; apply GlobalTheory.LocLanglands.hasPairEps_transport <;> assumption)
