module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompEqIdOfTwists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory


open Moduli.LevelAction in
theorem levMove_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (_c : Coeff l), ∀ (ρ ρ' : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ν' : SABMap Xo.univ.t Xo.univ.t ρ') (gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La), 1 ≤ Dw.p + Dw.q → (∀ a, gM a - gM' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA a - gA' a)) → IsIso ρ → IsIso ρ' → IsLevMove ρ ν gM gA → IsLevMove ρ' ν' gM' gA' → (∃ g : Sim Dw, (∀ a, g.f l.M a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) ∧ (∀ a, Dw.ModN l.A (g.f l.A a - gA a)) ∧ (l.A : ℤ) ∣ g.ν l.A - 1) → ρ = ρ' ∧ ν.φ = ν'.φ := by
  intro E _ _ _ H Dw l Xo _ ρ ρ' ν ν' gM gM' gA gA' hpq hM hA _ _ ⟨hs, e, eA⟩ ⟨hs', e', eA'⟩ ⟨g, hgM, hgA, hν⟩
  have hred : IsReduced Xo.X := by
    have := Xo.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s
      (SmoothOfRelativeDimension.smooth Dw.dim _)).1
  obtain ⟨o, m, a₁, b₁⟩ := exists_obj_twist_by_similitude SimAlg.sim_group E H Dw l _ _ _ _ Xo.univ g hpq hν
  obtain ⟨n, hn⟩ := Moduli.LevelAction.exists_comp_sabMap m ν (Category.id_comp ρ)
  obtain ⟨n', hn'⟩ := Moduli.LevelAction.exists_comp_sabMap m ν' (Category.id_comp ρ')
  have c₁ : ∀ a, (o.eta a).left ≫ n.φ = ρ ≫ (Xo.univ.eta a).left := fun a => by
    rw [hn, ← Category.assoc, a₁, Moduli.LevelAction.eta_congr Xo.univ (hgM a), e]
  have c₂ : ∀ a, (o.etaA a).left ≫ n.φ = ρ ≫ (Xo.univ.etaA a).left := fun a => by
    rw [hn, ← Category.assoc, b₁, Moduli.LevelAction.etaA_congr Xo.univ (hgA a), eA]
  have d₁ : ∀ a, (o.eta a).left ≫ n'.φ = ρ' ≫ (Xo.univ.eta a).left := fun a => by
    rw [hn', ← Category.assoc, a₁, Moduli.LevelAction.eta_congr Xo.univ (hgM a), Moduli.LevelAction.eta_congr Xo.univ (hM a), e']
  have d₂ : ∀ a, (o.etaA a).left ≫ n'.φ = ρ' ≫ (Xo.univ.etaA a).left := fun a => by
    rw [hn', ← Category.assoc, b₁, Moduli.LevelAction.etaA_congr Xo.univ (hgA a), Moduli.LevelAction.etaA_congr Xo.univ (hA a), eA']
  obtain rfl : ρ = ρ' := (Xo.rep _ Xo.s hred o).unique ⟨hs, ⟨⟨n, c₁, c₂⟩⟩⟩ ⟨hs', ⟨⟨n', d₁, d₂⟩⟩⟩
  refine ⟨rfl, ?_⟩
  have h := obj_rigid_closed firstFiveLaws.1 E H Dw l _ _ _ _ _ _ _ _ Xo.univ o ρ (Or.inl hred) n n'
    fun a => ⟨_, c₁ a, d₁ a⟩
  have : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  rw [hn, hn'] at h
  exact (cancel_epi m.φ).1 h

end GlobalTheory
