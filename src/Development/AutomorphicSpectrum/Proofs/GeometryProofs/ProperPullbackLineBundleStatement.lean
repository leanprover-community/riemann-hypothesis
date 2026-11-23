module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperPullbackLineBundle
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

theorem _root_.GlobalTheory.T.proper_pullback_line_bundle : ∀ (X₀ Xg X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξg : Spec (CommRingCat.of Ω) ⟶ Xg) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (L : Lat ξ Ω) (T : Set (Cpt ξ)) (t : Ω), IsPreimmersion e → IsProper f → IsLocallyNoetherian Xg → ξg ≫ e = ξ → ξ' ≫ f = ξg → IsCptGen ξ → NormalCpt ξ → (∀ x : Cpt ξ, x ∈ T ↔ x.1 ∈ Set.range e) → L.IsVBOn T 1 ⊤ → (∀ p' : Cpt ξ', (L.pull ξ' (f ≫ e) (AddMonoidHom.id _)).IsGenAt p' t) → ∀ x ∈ T, L.IsGenAt x t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PushLoc.gen_descends | exact GlobalTheory.CompanionTheory.Ar.Flat.PushLoc.gen_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PushLoc.gen_descends <;> assumption)
