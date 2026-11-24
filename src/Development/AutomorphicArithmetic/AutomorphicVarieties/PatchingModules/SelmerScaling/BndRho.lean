module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
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
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem bnd_of {A Fr Γ Γ' : Type} [CommRing A] [CommRing Fr] [Algebra A Fr] [TopologicalSpace Γ]
    [TopologicalSpace Γ'] (t : A) (φ : Γ' → A) (hφ : AdicCont (Ideal.span {t}) φ) (p : Γ → Γ') (hp : Continuous p) :
    BndF t fun g => algebraMap A Fr (φ (p g)) :=
  ⟨0, fun g => φ (p g), fun N => (hφ N).comp_continuous hp, fun g => by simp⟩

theorem UpperTheory.V.Pa.bndRho :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), BndM x.t (fun g : G.G₀ => x.ρX x.Fr (h.p₀ g)) ∧ BndM x.t (fun g : G.G₀ => x.ρX x.Fr (h.p₀ g⁻¹)) ∧ ∀ j, BndM x.t (kapF h k j) := by
  intro l _ L G G0 h n x k
  have hp : Continuous (h.p₀ : G.G₀ → G0.G₀) := by
    apply Continuous.subtype_mk
    exact h.cont.comp continuous_subtype_val
  have hpi : Continuous (fun g : G.G₀ => h.p₀ g⁻¹) := hp.comp continuous_inv
  have hρ : ∀ i j, AdicCont (Ideal.span {x.t}) (fun g : G0.G₀ => (mat x.ρ) g i j) := by
    intro i j
    have := x.cont i j
    rwa [PowerSeries.maximalIdeal_eq_span_X] at this
  refine ⟨fun i j => bnd_of x.t _ (hρ i j) _ hp, fun i j => bnd_of x.t _ (hρ i j) _ hpi, ?_⟩
  intro j i i'
  have hk := ((k.mem j).2.1 i i')
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hk
  exact bnd_of x.t _ hk _ hp
