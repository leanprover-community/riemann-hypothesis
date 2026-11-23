module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

noncomputable section

open Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.G3

structure IsFrame {k : Type} [Field k] {n : ℕ} (c : k →+* k) (δ : GL (Fin n) k) (s : k) {B : Type} [CommRing B] (d : B)
    (ρ : B →+* Matrix (Fin n) (Fin n) k) : Prop where
  inj : Function.Injective ρ
  sq : ρ d = (s ^ 2) • (1 : Matrix (Fin n) (Fin n) k)
  adj : ∀ a, ρ a * (δ.val * GlobalTheory.Tw.Phi n k) = δ.val * GlobalTheory.Tw.Phi n k * ((ρ a).map c)ᵀ
  comm : ∀ a, ρ a * (δ * thetaGL n c δ).val = (δ * thetaGL n c δ).val * ρ a
  span : ∀ x : Matrix (Fin n) (Fin n) k, x * (δ * thetaGL n c δ).val = (δ * thetaGL n c δ).val * x →
    ∃ a b, x = ρ a + s • ρ b

def pt {k : Type} [Field k] {n : ℕ} (δ : GL (Fin n) k) {B : Type} [CommRing B] (ρ : B →+* Matrix (Fin n) (Fin n) k)
    (t : Bˣ) : GL (Fin n) k := Units.map ρ.toMonoidHom t * δ

end PositivityTheory.Rg.BcB.G3

end
